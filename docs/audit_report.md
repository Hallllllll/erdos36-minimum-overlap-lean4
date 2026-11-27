# Lean audit of the minimum-overlap certificate

This audit covers the witness-only revision identified below. The current development proves the discrete limit theorem and its upper bound in [DiscreteUpper.lean](../Overlap/DiscreteUpper.lean). The current replay results are in the [benchmark report](benchmarks.md).
Audited revision `1aa6999c32a2866626b776fea2dc43cd52a8f999` with Lean 4.36.0 and Mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

## Findings

- Lean certifies the complete **18,815-entry** interior coefficient list, both zero endpoints and the zero exterior grid vertices. It bounds the actual Lebesgue overlap at **every real shift**, proves attainment at `(-2284 : ℝ) * width = -571/1176`, and proves that the supremum for this witness equals the exact rational `U`.
- The exhaustive strict comparisons for the **unique maximizing shift of this witness** come from Python. The affine identity then gives real-shift uniqueness as a mathematical corollary. The Lean witness theorems express the bound and attainment.
- Lean proves `continuousConstant ≤ U` from admissibility and the overlap bound. The conclusion about the original discrete limiting constant uses the explicit `WhiteBridge` and `hc` hypotheses. The theorem gives an upper bound for the infimum and leaves the value of the infimum and the witness's optimality open.
- README and CI replay the same **eight** named proof modules, matching the full transitive set imported by the top-level `Overlap` entry point. The repository has ten Lean source modules in total, counting the entry point and the separate `Overlap.Bench` sample. [README](../README.md#kernel-audit) · [CI](../.github/workflows/verify.yml#L33-L51)

## Definitions and imports

Here `N = 9408`, `D = 52428700000000`, `B = 2^128`, `width = 2 / (N : ℝ) = 1/4704`, and `U = 2462273619527794579322422405079 / 6465103708838880000000000000000`. The numerator list `nums` is `heights.items`. `step` sums indicators of half-open bins `[iw,(i+1)w)`. The witness `h` has heights `aᵢ/D` and `g` has heights `(D-aᵢ)/D`. The latter subtraction is on naturals. The height-box certificate permits casting it to real subtraction in the proof of the pointwise identity `g = complement h`. The complement is the indicator of `[0,2)` times `1-f`, including the zero extension. [Numerical](../Overlap/Numerical.lean#L8-L19) · [AffineBridge](../Overlap/AffineBridge.lean#L10-L19) · [Profile](../Overlap/Profile.lean#L56-L57) · [Main](../Overlap/Main.lean#L11-L32)

`Admissible f` requires measurability, pointwise `0 ≤ f x ≤ 1`, pointwise zero outside `[0,2)`, and Lebesgue integral one. `overlap f g s` is the real Lebesgue integral of `f x * g (x-s)`. `continuousConstant` is the real infimum of the set of objective values `sSup (Set.range (overlap f (complement f)))` for admissible `f`. Both the witness and the continuous objective use the ordinary supremum over real shifts. [Spec](../Overlap/Spec.lean#L8-L14) · [AffineBridge](../Overlap/AffineBridge.lean#L16)

The discrete sites are `Fin (2*n)`, which translates the usual labels by one and preserves `a-b`. `multiplicity` filters the cartesian product of `A` and `univ \ A` by that signed difference. `minimumOverlap` takes a natural infimum over the indexed suprema for `A.card = n`. `minimumOverlap_le_iff` checks the intended finite interpretation using existence of an `n`-element subset and boundedness of each multiplicity range by the cross-product cardinality. For positive `n`, all nonzero multiplicities occur at `-2*n < k < 2*n`, so quantifying over all integers gives the same maximum. The Lean definition also covers `n = 0`, which is immaterial to the `atTop` limit. [Spec](../Overlap/Spec.lean#L16-L43)

The import table follows the order of imports in each source file.

| File | Direct imports | Role |
| --- | --- | --- |
| [Overlap.lean](../Overlap.lean) | `Overlap.Main` | Library entry point |
| [Tree](../Overlap/Tree.lean) | `Init` | Natural-valued trees, size, sum, maximum, packing and flattening |
| [Data](../Overlap/Data.lean) | `Overlap.Tree` | Generated literals. 294 height chunks and 588 digit chunks, each assembled into one tree |
| [Numerical](../Overlap/Numerical.lean) | `Overlap.Data` | Seven concrete `decide +kernel` certificates |
| [Algebra](../Overlap/Algebra.lean) | `Mathlib.Data.Nat.Digits.Lemmas`, `Mathlib.Algebra.BigOperators.Fin`, `Mathlib.Tactic`, `Overlap.Tree` | General coefficient formula, carry bound and fixed-length digit injectivity |
| [AffineBridge](../Overlap/AffineBridge.lean) | `Mathlib.MeasureTheory.Integral.Bochner.Set`, `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`, `Mathlib.Tactic` | Pairwise integrals, affine interpolation and generic grid supremum |
| [Profile](../Overlap/Profile.lean) | `Overlap.AffineBridge`, `Overlap.Algebra` | Integrals and support of step functions, scaled integer coefficients |
| [Spec](../Overlap/Spec.lean) | `Overlap.AffineBridge` | Continuous and discrete definitions and external bridge proposition |
| [Main](../Overlap/Main.lean) | `Overlap.Numerical`, `Overlap.Profile`, `Overlap.Spec` | Witness-specific results and final implications |
| [Bench](../Overlap/Bench.lean) | `Overlap.Tree` | Generated 64-height sample and 127-entry product check, outside the entry point's import closure |

## Exhaustive integer certificate

1. `Tree.items` lists left before right, with the left subtree holding the lower powers of the base. `Tree.pack_eq` identifies this number with `Nat.ofDigits B`. `Tree.other_eq` does the same for the reversed list of complements. `packed_events` expands the product by finite sums and assigns each pair `(i,j)` exactly once, to the exponent `i + (N-1-j)`. Thus the natural-valued `event` at index `N-1+k` is the sum of `aᵢ(D-aⱼ)` over pairs with `i-j=k`. [Tree](../Overlap/Tree.lean#L24-L35) · [Algebra](../Overlap/Algebra.lean#L29-L73) · [Product identity](../Overlap/Algebra.lean#L96-L118)
2. `event_lt` uses a conservative bound of `N²D² < B` on every true coefficient by bounding all `N²` pair contributions. The sharper `ND²` follows because each lag fixes at most one `j` per `i`. The supplied digits are each at most `peak = 4924547239055589158644844810158 < B` by the tree maximum. The use of an exact length `2*N-1` preserves any high-order zeros. `digits_certified` checks both lists' lengths and digit bounds, then applies `Nat.ofDigits_inj_of_len_eq` to the packed equality. The result is equality of the **entire** true and supplied lists. `all_events_le` transfers the maximum bound to every valid index. [Carry bound](../Overlap/Algebra.lean#L75-L86) · [List equality and bound](../Overlap/Algebra.lean#L120-L140)
3. `Numerical` evaluates the closed height count, height box, height mass, digit count, digit maximum, packed equality and lookup at zero-based index 7123 using `decide +kernel`. This checks the embedded integers directly in Lean. The product equality alone would allow carries or ambiguities from omitted zeros, which the algebraic side conditions rule out. Indices `0…18814` encode lags `-9407…9407`. Lags `±9408` and all further integer lags are zero by `vertex_outside`. The number 18,817 includes both endpoints. [Numerical](../Overlap/Numerical.lean#L13-L19) · [Exterior vertices](../Overlap/AffineBridge.lean#L107-L113)

## From the grid to the real supremum

1. `pair_fun` expresses the product of two bin indicators as a constant times the indicator of their intersection at the signed shift. `pair_integrable` justifies summing the integrals. `pair_int` evaluates each as its constant times the nonnegative intersection length. For `s=(k+u)w` and `0≤u≤1`, `unit_length` gives the only potentially nonzero contributions, with lengths `(1-u)w` at `i-j=k` and `uw` at `i-j=k+1`. Summing yields the exact affine identity, including both endpoints. Every real shift has such a representation by `floor_partition` when `w>0`. The two weights are nonnegative and sum to one. [AffineBridge](../Overlap/AffineBridge.lean#L21-L105)
2. `vertex_event` proves the grid value equals the matching digit times `w/D² = 2/(ND²)` for interior lags. `witness_vertex_bound` handles the exterior and endpoints by zero, and the interior by `all_events_le`. `witness_all_shifts` transfers this bound to every real shift via `continuous_le`. The same affine formula and zero exterior vertices give zero for `|s| ≥ 2`. The generic `grid_supremum` proves existence of a grid maximizer even for signed heights, by including a zero endpoint. `Main` obtains its witness result directly from the all-shifts bound and the attaining value. [Profile](../Overlap/Profile.lean#L66-L81) · [Main](../Overlap/Main.lean#L54-L100) · [Generic grid maximum](../Overlap/AffineBridge.lean#L115-L135)
3. `witness_peak_value` transfers digit 7123 through list equality, converts `7123 = N-1-2284` to the signed lag, and scales its exact value to `U`. The range of the real overlap is nonempty, is bounded above by `U`, and contains `U`. The two conditional-supremum inequalities therefore give equality. This is an attained supremum for the specified witness. The admissibility proof is a separate use of the height count, height box, and mass identity. [Main](../Overlap/Main.lean#L16-L50) · [Attainment and supremum](../Overlap/Main.lean#L71-L100)
4. For the infimum over profiles, every admissible objective is nonnegative by pointwise nonnegativity of the integrand and the supremum lemma for reals. This provides the lower bound on the set needed for `csInf_le`. The witness gives a member of that set and its upper bound yields `continuousConstant ≤ U`. The implication already follows from `witness_supremum_bound`. [Main](../Overlap/Main.lean#L106-L122)

### Uniqueness and the sign of the shift

The direct Python audit computes every signed vertex using exact integer dot products and checks that the maximum occurs only at lag `-2284`. In the embedded integer list, the runner-up is lag `-3052` with coefficient `4924547239052075910263140700146`. Since the cap is positive, the exterior cannot attain it. In the open interior of any grid segment, both weights are strictly positive. At least one endpoint is strictly below the cap because only one vertex attains it. The affine formula therefore makes every off-grid value strictly smaller. This establishes uniqueness for the exhibited profile by combining the finite exact comparisons with the interpolation theorem. The Lean results include no strict inequality test against all other digits and no declaration of unique attainment. [Direct scan](../audit_verify.py#L77-L108) · [Interpolation](../Overlap/AffineBridge.lean#L69-L84) · [Lean attainment](../Overlap/Main.lean#L80-L100)

The sign is tied to the convention `g(x-s)`, for which aligning bins gives `i-j=k`. Under `g(x+t)`, the same maximum occurs at `t=+571/1176` by substituting `s=-t`. `plus_shift_bound` itself states the corresponding bound for every `t`. [Main](../Overlap/Main.lean#L80-L104)

## Hypotheses and verification boundary

`WhiteBridge` is a definition of the proposition that `(minimumOverlap n : ℝ) / n` tends to `continuousConstant`. It supplies convergence as well as its continuous value. Given `hc` for an arbitrary `c`, `tendsto_nhds_unique hc white` identifies `c` with `continuousConstant`, then the theorem applies the continuous bound. `hc` names the limit appearing in the conclusion. The contents of `WhiteBridge` are external mathematical input to this invocation, and its occurrence as a binder is compatible with the ordinary axiom list printed for the theorem. The name `white` denotes the local hypothesis. [Definition](../Overlap/Spec.lean#L41-L43) · [Implication](../Overlap/Main.lean#L124-L128)

White's introduction attributes convergence to Haugland and the continuous characterization to Swinnerton-Dyer, referring to Haugland for its proof. Equation (1.1) uses `[-1,1]` and a plus shift. Translation by one gives `[0,2]`, adjusting an endpoint changes only a null set for any fixed shift, and sign reversal preserves the shift supremum. With both factors extended by zero, the overlap vanishes for shifts outside `[-2,2]` and is nonnegative, so using all real shifts preserves the objective. These are the convention checks behind applying the published characterization to the Lean proposition. [White, equation (1.1) and introduction](https://arxiv.org/html/2201.05704#S1) · [Repository derivation](../PROOF.md#L19-L27)

`Numerical` imports `Data`, `Data` imports `Tree`, and `Tree` imports `Init`. The concrete multiplication is axiom-free. The general identification of the coefficient list and the real analysis use Lean and Mathlib. The relevant theorem dependency closures use the standard axioms shown below, with no `sorryAx` or custom axioms. Python, JSON, SHA-256, the generator, parent provenance, decimal enclosures and the parent improvement are outside the Lean theorem dependency chain. Byte-for-byte regeneration links the checked literals to the JSON inputs. Both Python programs recompute the parent rational score from the local parent heights. One uses integer packing. The independent audit uses direct sums with separate formulas for both signs. [Generator](../scripts/generate.py) · [Packed verifier](../verify.py) · [Direct audit](../audit_verify.py)

## Build and replay evidence

- Independently enumerated the ten tracked Lean files, walked their local imports, and compared the result with both replay loops. The nine files under `Overlap/` are the eight transitive proof imports plus `Bench`. Adding `Overlap.lean` gives ten. The default target is `Overlap`. CI fetches the Mathlib cache, builds the default target, replays the eight proof modules in individual processes, runs both Python verifiers, and checks regeneration of `Data.lean` and `Bench.lean`. [Lake configuration](../lakefile.toml) · [README](../README.md#L30-L48) · [CI](../.github/workflows/verify.yml#L30-L51)
- The canonical release-repository run `20261127T033045Z` records status 0 for the project clean, the default `Overlap` build, and each of the eight individual `leanchecker` replays for `Tree`, `Data`, `Numerical`, `Algebra`, `AffineBridge`, `Profile`, `Spec`, and `Main`. The measurements index records each command, exit status, and raw log filename. [Project clean](../benchmarks/results/20261127T033045Z/11-clean-project-before-default-build.log) · [Default build](../benchmarks/results/20261127T033045Z/12-default_build-Overlap.log) · [Build and replay index](../benchmarks/results/20261127T033045Z/measurements.jsonl)
- `Overlap.Bench` is the distinct 64-height, 127-coefficient sample. It sits outside the core import closure and CI's eight-module replay list. The release-repository run built it separately after the default build and replayed it successfully. Its checked product has zero axiom dependencies. [Sample source](../Overlap/Bench.lean) · [Separate build](../benchmarks/results/20261127T033045Z/13-build_after_default-Bench.log) · [Separate replay](../benchmarks/results/20261127T033045Z/22-leanchecker-Bench.log)
- The release axiom capture confirms the three headline signatures below. It records zero axioms for `packed_certificate`, `propext` for `peak_digit`, and the standard three axioms for the headline theorems. [Release axiom capture](../paper/validation/axioms.txt)
- The release digit-guard run accepts the original packed equality and rejects it after one coefficient is changed. Appending a high-order zero preserves the packed value and fails the fixed-length check. The two-digit example `[B, 0]` has the same packed value and length as `[0, 1]`, and the former fails the digit-range check. These outcomes exercise the independent checks used in fixed-length digit recovery. [Guard results](../paper/validation/digit-guards.txt) · [Guard statements](../scripts/check_digit_guards.py#L14-L31)
- Both Python verifiers passed in the audit. A read-only invocation of the generator captured its two outputs in memory and matched them byte for byte against both tracked Lean files. Parsing all generated leaves separately confirmed 9,408 heights, their sum of 246624604800000000, and 18,815 packed digits.

## Exact Lean output

The following is the default Lean pretty-printer output from `#check` through `import Overlap`. The concrete calculation and the generic transfer lemmas appear alongside the public conclusions.

```text
Overlap.Admissible (f : ℝ → ℝ) : Prop
Overlap.complement (f : ℝ → ℝ) (x : ℝ) : ℝ
Overlap.continuousConstant : ℝ
Overlap.multiplicity (n : ℕ) (A : Finset (Fin (2 * n))) (k : ℤ) : ℕ
Overlap.minimumOverlap (n : ℕ) : ℕ
Overlap.WhiteBridge : Prop
Overlap.minimumOverlap_le_iff (n m : ℕ) :
  Overlap.minimumOverlap n ≤ m ↔ ∃ A, A.card = n ∧ ∀ (k : ℤ), Overlap.multiplicity n A k ≤ m
Overlap.height_count : Overlap.heights.size = Overlap.N
Overlap.height_box : Overlap.heights.high ≤ Overlap.D
Overlap.height_mass : 2 * Overlap.heights.total = Overlap.N * Overlap.D
Overlap.event_count : Overlap.events.size = 2 * Overlap.N - 1
Overlap.event_peak : Overlap.events.high = Overlap.peak
Overlap.packed_certificate :
  Overlap.Tree.pack Overlap.B Overlap.heights * Overlap.Tree.other Overlap.B Overlap.D Overlap.heights =
    Overlap.Tree.pack Overlap.B Overlap.events
Overlap.peak_digit : Overlap.events.items[7123]? = some Overlap.peak
Overlap.event (a : List ℕ) (d k : ℕ) : ℕ
Overlap.exactDigits (a : List ℕ) (d : ℕ) : List ℕ
Overlap.event_lt {a : List ℕ} {d b : ℕ} (ha : ∀ x ∈ a, x ≤ d) (hb : a.length * a.length * d * d < b) (k : ℕ) :
  Overlap.event a d k < b
Overlap.packed_events (a : List ℕ) (b d : ℕ) :
  Nat.ofDigits b (Overlap.exactDigits a d) = Nat.ofDigits b a * Nat.ofDigits b (List.map (fun x => d - x) a).reverse
Overlap.digits_certified {t c : Overlap.Tree} {b d p : ℕ} (hB : 1 < b) (hbox : t.high ≤ d)
  (hsize : t.size * t.size * d * d < b) (hc : c.high ≤ p) (hp : p < b) (hn : c.size = 2 * t.size - 1)
  (hm : Overlap.Tree.pack b t * Overlap.Tree.other b d t = Overlap.Tree.pack b c) :
  Overlap.exactDigits t.items d = c.items
Overlap.all_events_le {t c : Overlap.Tree} {b d p : ℕ} (hB : 1 < b) (hbox : t.high ≤ d)
  (hsize : t.size * t.size * d * d < b) (hc : c.high ≤ p) (hp : p < b) (hn : c.size = 2 * t.size - 1)
  (hm : Overlap.Tree.pack b t * Overlap.Tree.other b d t = Overlap.Tree.pack b c) (k : Fin (2 * t.items.length - 1)) :
  Overlap.event t.items d ↑k ≤ p
Overlap.affine {n : ℕ} (w : ℝ) (hw : 0 ≤ w) (v z : Fin n → ℝ) (k : ℤ) (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
  Overlap.overlap (Overlap.step w v) (Overlap.step w z) ((↑k + u) * w) =
    (1 - u) * Overlap.vertex w v z k + u * Overlap.vertex w v z (k + 1)
Overlap.floor_partition (s w : ℝ) (hw : 0 < w) : ∃ k u, 0 ≤ u ∧ u ≤ 1 ∧ s = (↑k + u) * w
Overlap.grid_value {n : ℕ} (w : ℝ) (hw : 0 ≤ w) (v z : Fin n → ℝ) (k : ℤ) :
  Overlap.overlap (Overlap.step w v) (Overlap.step w z) (↑k * w) = Overlap.vertex w v z k
Overlap.vertex_outside {n : ℕ} (w : ℝ) (v z : Fin n → ℝ) (k : ℤ) (hk : k ≤ -↑n ∨ ↑n ≤ k) : Overlap.vertex w v z k = 0
Overlap.grid_supremum {n : ℕ} (w : ℝ) (hw : 0 < w) (v z : Fin n → ℝ) :
  ∃ k ∈ Finset.Icc (-↑n) ↑n,
    (∀ j ∈ Finset.Icc (-↑n) ↑n, Overlap.vertex w v z j ≤ Overlap.vertex w v z k) ∧
      sSup (Set.range (Overlap.overlap (Overlap.step w v) (Overlap.step w z))) = Overlap.vertex w v z k
Overlap.vertex_event (a : List ℕ) (d : ℕ) (w : ℝ) (k : ℤ) (hk : -↑a.length < k) (_hk' : k < ↑a.length) :
  Overlap.vertex w (Overlap.values a d) (Overlap.remaining a d) k =
    ↑(Overlap.event a d (k + ↑a.length - 1).toNat) * (w / ↑d ^ 2)
Overlap.complement_h : Overlap.g = Overlap.complement Overlap.h
Overlap.admissible_h : Overlap.Admissible Overlap.h
Overlap.witness_vertex_bound (k : ℤ) :
  Overlap.vertex Overlap.width (Overlap.values Overlap.nums Overlap.D) (Overlap.remaining Overlap.nums Overlap.D) k ≤
    Overlap.U
Overlap.witness_all_shifts (s : ℝ) : Overlap.overlap Overlap.h (Overlap.complement Overlap.h) s ≤ Overlap.U
Overlap.witness_peak_value :
  Overlap.overlap Overlap.h (Overlap.complement Overlap.h) (-2284 * Overlap.width) = Overlap.U
Overlap.witness_supremum_bound :
  sSup (Set.range (Overlap.overlap Overlap.h (Overlap.complement Overlap.h))) ≤
    2462273619527794579322422405079 / 6465103708838880000000000000000
Overlap.witness_supremum_exact : sSup (Set.range (Overlap.overlap Overlap.h (Overlap.complement Overlap.h))) = Overlap.U
Overlap.plus_shift_bound (t : ℝ) : ∫ (x : ℝ), Overlap.h x * Overlap.complement Overlap.h (x + t) ≤ Overlap.U
Overlap.continuous_upper_bound :
  Overlap.continuousConstant ≤ 2462273619527794579322422405079 / 6465103708838880000000000000000
Overlap.discrete_upper_bound_of_white {c : ℝ}
  (hc : Filter.Tendsto (fun n => ↑(Overlap.minimumOverlap n) / ↑n) Filter.atTop (nhds c))
  (white : Overlap.WhiteBridge) : c ≤ 2462273619527794579322422405079 / 6465103708838880000000000000000
```

These lines are verbatim `#print axioms` output from the audit probe. The last line is from checking `Overlap/Bench.lean` directly. The canonical release capture independently confirms the entries it covers. Six of the seven concrete certificate declarations are axiom-free. The indexed lookup `peak_digit` depends on `propext`. [Release axiom capture](../paper/validation/axioms.txt) · [Bench build output](../benchmarks/results/20261127T033045Z/13-build_after_default-Bench.log)

```text
'Overlap.height_count' does not depend on any axioms
'Overlap.height_box' does not depend on any axioms
'Overlap.height_mass' does not depend on any axioms
'Overlap.event_count' does not depend on any axioms
'Overlap.event_peak' does not depend on any axioms
'Overlap.packed_certificate' does not depend on any axioms
'Overlap.peak_digit' depends on axioms: [propext]
'Overlap.packed_events' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.digits_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.all_events_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.grid_supremum' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.vertex_event' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.minimumOverlap_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.admissible_h' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.witness_all_shifts' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.witness_peak_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.witness_supremum_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.continuous_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.discrete_upper_bound_of_white' depends on axioms: [propext, Classical.choice, Quot.sound]
'Overlap.sample_product' does not depend on any axioms
```
