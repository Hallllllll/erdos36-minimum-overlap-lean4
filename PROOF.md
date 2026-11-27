# Erdős Problem 36: A rational upper bound for the minimum overlap constant

The explicit profile in `construction.json` proves

$$
 c\ \le\ Q=\frac{2462273619527794579322422405079}{6465103708838880000000000000000}
 \ <\ 0.38085601258978320592.
$$

The parent profile is the November 25, 2026 Compute Substrate entry descended from EinsteinArena’s Blob. Its 4,704 heights give the exact score $P=123113681346619/323255185441944$. The gain is

$$
P-Q=\frac{2468195140225859198307}{2155034569612960000000000000000}
\ >\ 0.00000000114531579911.
$$

The new profile descends directly from that entry. The parent integers are included in `sources/frontier_parent.txt`. [Parent proposal](https://explorer.computesubstrate.org/proposal.html?id=0x61ac9b0230694a2da6c369e7518c7ad186d2613659f85b1ae9c2b6f1f8f13b7e) · [Original parent integers on ArDrive](https://ardrive.net/IYS-L1CFuiB-2krt6PDvWIvQoztzBqE-9AvvLyfNBdY)

As a public upper bound, $Q$ was superseded on November 27, 2026 by an 18,816-cell step function posted by `willk30` in open PR #419 to `teorth/optimizationproblems` with published exact rational bound $270730612195671389820648367/710848381933401954727231488 < 0.3808556355$, which AI-assisted verification scripts in this session also recomputed with exact packed integers from its 18,816-height dataset. The Erdős Problem a Day review (`44a4n7`) independently recomputed both $Q$ (confirming the exact value, unique maximizing shift $s=-571/1176$, side conditions, parent gain, and Lean-to-data equality for v1.0.0) and the superseding #419 bound, and read the Lean sources for `sorry`, `native_decide`, and custom axioms. That review reported independent witness verification and source inspection for v1.0.0, while local Lean builds of v1.0.0 and commit `31ded31` remained outside that review. [Erdős Problem a Day article](https://erdosproblemaday.com/day/36-minimum-overlap-reader-bound-checked-and-the-record-race) · [Review 44a4n7](https://erdosproblemaday.com/submission/44a4n7)

## From a profile to an upper bound

Let $M(n)$ be the minimum, over partitions $A\sqcup B=\{1,\ldots,2n\}$ with $|A|=|B|=n$, of the maximum over integer lags $k$ of the number of pairs $(a,b)\in A\times B$ with $a-b=k$. Write $c=\lim_{n\to\infty}M(n)/n$. Swinnerton-Dyer's theorem, proved in Haugland (1996), identifies $c$ with the infimum of $\sup_s H_f(s)$ over measurable densities $f$ on $[0,2)$ with $0\le f\le1$ and integral one. White (2022/2023) equation (1.1) states that continuous variational formulation and summarizes Swinnerton-Dyer's theorem in the introduction. Here $g=1-f$ on that interval, both functions are zero outside it, and

$$
H_f(s)=\int_{\mathbb R} f(t)g(t-s)\,dt.
$$

The sign agrees with $a-b=k$ because the second coordinate is the first minus the lag. Translating White’s interval $[-1,1]$ by one preserves the integral and every shift. Changing the value at the right endpoint has no effect on the integral, and White’s use of $g(t+x)$ corresponds to $x=-s$, which preserves the supremum. [Haugland (1996)](https://doi.org/10.1006/jnth.1996.0064) · [White (2022/2023), eq. (1.1)](https://arxiv.org/html/2201.05704#S1)

Let $N=9408$, $D=52428700000000$ and $w=2/N$. In zero-based order, let $a_i$ be the integers in `construction.json`. On $[iw,(i+1)w)$ set $f=a_i/D$. Exact integer arithmetic verifies $0\le a_i\le D$ and $2\sum_i a_i=ND$. Thus $\int f=1$.

At the shift $s=kw$, entire cells align. In units of $w/D^2$, the overlap is the nonnegative integer

$$
 T_k=\sum_{\substack{0\le i<N\\0\le i-k<N}} a_i(D-a_{i-k}).
$$

For $s=(k+u)w$ with $0\le u\le1$, write $t=(i+v)w$ on cell $i$. When $v<u$ the argument $t-s$ lies in cell $i-k-1$, and when $v\ge u$ it lies in cell $i-k$, apart from endpoints of measure zero. The respective lengths are $uw$ and $(1-u)w$. Zero extension applies whenever the complementary cell is outside the support. Hence

$$
 H_f((k+u)w)=\frac{2}{ND^2}\big((1-u)T_k+uT_{k+1}\big).
$$

The function therefore attains its maximum at a checked vertex. It vanishes for $|s|\ge2$. The interior cell boundaries and the choice of open or closed endpoints do not change the integral.

## Exact maximum

Across all $2N+1=18817$ signed vertices, including the two zero endpoints, the unique maximizing bin lag is $k=-2284$, or $s=-571/1176$. Its integer numerator is $4924547239055589158644844810158$. Multiplication by $2/(ND^2)$ gives $Q$. Every other vertex is strictly smaller. Since this admissible profile is among those in the continuous infimum, $c\le Q$.

## Fixed-length carry-free packing

Consider the two integer polynomials

$$
A(z)=\sum_{i=0}^{N-1} a_i z^i,
\qquad
B(z)=\sum_{j=0}^{N-1}(D-a_j)z^{N-1-j}.
$$

The coefficient at index $N-1+k$ of their product is $T_k$, because the exponents add to $N-1+i-j$. Thus indices $0,\ldots,2N-2$ encode the interior lags $-(N-1),\ldots,N-1$. Each coefficient lies between zero and $ND^2$, since at most $N$ pairs contribute and each product is at most $D^2$.

For the Lean certificate, evaluate both polynomials at the integer base $b=2^{128}$. The code uses the bound $N^2D^2<b$, which also implies $ND^2<b$. The product therefore encodes the coefficients without carries. The certificate supplies exactly $2N-1$ digits in increasing exponent order, including high-order zeros, and checks that each digit is below $b$ and that the packed value equals $A(b)B(b)$. Uniqueness of digits in base $b$ at this fixed length identifies the entire list with the true coefficients. The two zero endpoints are supplied by the support calculation.

The independent audit computes $C_k=\sum_{i=0}^{N-1-k}a_i a_{i+k}$ directly for $0\le k\le N$. It then obtains both signs separately,

$$
 T_{+k}=D\sum_{i=k}^{N-1}a_i-C_k,\qquad
 T_{-k}=D\sum_{i=0}^{N-1-k}a_i-C_k.
$$

As an additional check, $\sum_k T_k=(\sum_i a_i)(ND-\sum_i a_i)$. The audit checks the resulting vertex list against its digest and verifies the unique peak, the exact parent score, and the gain. The same grid and interpolation argument with the parent’s own cell count and denominator gives the parent’s continuous maximum.

## Lean proof scope

- `Overlap/Algebra.lean` proves fixed-length digit recovery. `Overlap/Numerical.lean` checks the embedded height count, bounds and mass, and the packed product, digit count, maximum digit, and digit at index $7123=N-1-2284$ using `decide +kernel`.
- `Overlap/Profile.lean` connects the integer events to the real grid values. `Overlap/AffineBridge.lean` proves the interpolation and reduction from real shifts to grid vertices.
- `Overlap/Main.lean` proves admissibility (`admissible_h`), the bound at every real shift (`witness_all_shifts`), attainment (`witness_peak_value`), the exact supremum (`witness_supremum_exact`), and the continuous upper bound (`continuous_upper_bound`). Its cleaned-up `discrete_upper_bound_of_white` takes `(white : WhiteBridge)` only (with no `hc` premise) and bounds $\limsup_{n\to\infty} M(n)/n \le Q$. The Python replay checks peak uniqueness and the parent comparison. Lean checks the embedded integers directly, independently of the Python generator and file hashes.
- `Overlap/Spec.lean` defines `minimumOverlap n` on `Fin (2 * n)`. `Overlap/DiscreteUpper.lean` provides the unconditional alternative from commit `31ded31`, proving that the discrete limsup is at most the continuous infimum (`discrete_limsup_le_continuous`), that the discrete limsup is at most $Q$ (`discrete_upper_bound`), and that the whole sequence converges to the continuous infimum (`whiteBridge`). The value of the infimum and the optimality of this particular profile remain open.
- `Overlap/FormalConjecturesDefs.lean` contains a verbatim extraction of the four `Erdos36` definitions (`Overlap`, `MaxOverlap`, `M`, `MinOverlapQuotient`) from `google-deepmind/formal-conjectures` commit `ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8` (upstream pins Lean 4.33.1 vs our Lean 4.36.0, so only the import list is adapted, and `scripts/check_formal_conjectures.sh` verifies the four declaration texts byte-for-byte against upstream in CI). `Overlap/FormalConjecturesBridge.lean` proves `Overlap.minimumOverlap_eq_erdos36 (n : ℕ) : minimumOverlap n = Erdos36.M n` for all `n` (including `n = 0`) and `Overlap.erdos36_discrete_upper_bound` directly on `Erdos36.MinOverlapQuotient`.

## Passing between densities and balanced partitions

For an admissible density, average its values on the $2n$ half-open cells of width $1/n$. The cell heights sum to exactly $n$. As the mesh tends to zero, these step functions converge in the integral of absolute error. Continuous approximation on the bounded support provides the estimate even for a merely measurable density. Changing the density by $L^1$ error $e$ changes each overlap by at most $2e$, uniformly over the shift. [Cell approximation](Overlap/CellApprox.lean)

Include mass and all interior signed lags among the rounding constraints. A nonzero lag gives a sum of terms $x_i(1-x_j)$ with $i-j=k$. It is affine in each coordinate separately. Changing one coordinate changes at most two summands, each by at most one. Use the constant zero for the discrete zero lag, since a site cannot belong to both parts. For $n>0$ there are $4n$ constraints altogether. A fourth-degree potential lets us fix one coordinate at a time and obtain a Boolean vector with fourth power of each error at most $2048n^3+384n^2$. If $t$ bounds their absolute errors, correcting the cardinality takes at most $t$ flips, adding at most $2t$ to any count. After division by $n$ the rounding error tends to zero. Taking the infimum over densities gives the upper half of the limit theorem. [Quartic potential](Overlap/QuarticRounding.lean) · [Signed lags and balancing](Overlap/LagRounding.lean)

Conversely, represent a balanced minimizer on $2n$ sites by an indicator step function of cell width $1/n$. Its vertex at $k/n$ is precisely the discrete multiplicity divided by $n$. Interpolation bounds the whole profile by $M(n)/n$. Thus the continuous infimum lies below every positive-index ratio. Together the two inequalities prove convergence. [Grid embedding](Overlap/GridLower.lean) · [Limit theorem](Overlap/DiscreteUpper.lean)

## Reproduce from the repository root

Run the two offline Python checks with the standard library and assertions enabled.

```sh
python3 -I -S -B verify.py
python3 -I -S -B audit_verify.py
```

`certificate.json` records both rational scores, their difference, the maximizing lag, decimal enclosures, and digests.

With Elan available, use the pinned Lean toolchain and Mathlib dependency. Fetch the Mathlib cache on a fresh checkout, build the default target `Overlap` (and `Overlap.Bench` for the 64-cell benchmark module), replay each named module under `Overlap/` in a fresh process, and run the axiom audit.

```sh
lake exe cache get
bash scripts/check_formal_conjectures.sh
lake build
lake build Overlap.Bench
ulimit -s unlimited
export LEAN_NUM_THREADS=1
for module in \
  Tree PackedConvolution ConvolutionExample Data Numerical Algebra \
  AffineBridge Profile Spec Main QuarticRounding CellApprox GridLower \
  LagRounding DiscreteUpper FormalConjecturesDefs FormalConjecturesBridge Bench; do
  lake env leanchecker "Overlap.$module" || exit 1
done
lake env lean scripts/paper_axioms.lean
```

For an optional full import-closure replay of all transitive Lean and Mathlib constants into an empty kernel environment, run `export LEAN_NUM_THREADS=1; ulimit -s 131072; lake env leanchecker --fresh Overlap` (the commit `31ded31` raw run is archived in `benchmarks/results/linux-fresh-root/`). `Overlap.lean` contains only four imports and no authored declarations, and the plain non-`--fresh` collective-prefix invocation `lake env leanchecker Overlap` is omitted because Lean 4.36.0 exits 139 while matching the `Overlap` namespace prefix (`paper/validation/root-aggregate-139.txt`).
