"""Independent audit by direct integer dot products and piecewise-affine geometry."""
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import accumulate, combinations
from math import comb
from pathlib import Path
from random import Random
import json
import sys

if not __debug__:
    raise SystemExit('Run with assertions enabled.')

def all_shifts(a, d):
    n = len(a)
    assert n and type(d) is int and d > 0
    assert all(type(t) is int and 0 <= t <= d for t in a)
    assert 2*sum(a) == n*d
    prefix = [0,*accumulate(a)]
    values = [0]*(2*n+1)
    for k in range(n+1):
        # A pair separated by k contributes the same quadratic term to either sign.
        common = sum(u*v for u,v in zip(a, a[k:]))
        values[n+k] = d*(prefix[n]-prefix[k])-common
        values[n-k] = d*prefix[n-k]-common
    assert values[0] == values[-1] == 0 and min(values) >= 0
    assert sum(values) == sum(a)*(n*d-sum(a))
    return values

def score(values,n,d):
    return F(2*max(values),n*d*d)

def geometry(n):
    # Represent an affine function by its values at 0 and 1. A branch is
    # valid throughout the unit interval if it wins at both endpoints.
    def lower(a,b):
        if a[0] <= b[0] and a[1] <= b[1]:
            return a
        assert b[0] <= a[0] and b[1] <= a[1], 'unaccounted interior crossing'
        return b
    def upper(a,b):
        return b if lower(a,b) == a else a
    for m in range(-2*n-1,2*n+2):
        # Length of [0,1] intersect [m+u,m+1+u].
        lo = upper((0,0),(m,m+1))
        hi = lower((1,1),(m+1,m+2))
        length = upper((0,0),(hi[0]-lo[0],hi[1]-lo[1]))
        assert length == {-1:(0,1),0:(1,0)}.get(m,(0,0))

def controls(root):
    rng = Random(36)
    for a,d in [([1],2),([0,2],2),([0,2,1,1],2)] + [
            (rng.sample([0,1,2,3,4,5,6],7),6) for _ in range(6)]:
        n = len(a)
        values = all_shifts(a,d)
        for k in range(-n-1,n+1):
            for u in (F(0),F(2,7),F(1,2),F(1)):
                s = k+u
                literal = sum(a[i]*(d-a[j])*max(0,min(i+1,j+1+s)-max(i,j+s))
                              for i in range(n) for j in range(n))
                def vertex(k):
                    return values[n+k] if -n <= k <= n else 0
                assert literal == (1-u)*vertex(k)+u*vertex(k+1)
    for row in json.loads((root/'small_cases.json').read_text()):
        n = row['n']
        universe = set(range(1,2*n+1))
        counts = Counter()
        for subset in combinations(universe,n):
            b = universe.difference(subset)
            t = Counter(i-j for i in subset for j in b)
            assert t[0] == 0 and sum(t.values()) == n*n
            counts[max(t.values())] += 1
        assert sum(counts.values()) == comb(2*n,n) and min(counts) == row['opt']
        assert counts == {int(k):v for k,v in row['hist'].items()}

def audit(root):
    raw = (root/'construction.json').read_bytes()
    obj = json.loads(raw)
    d,a = obj['denominator'],obj['numerators']
    n = len(a)
    meta = json.loads((root/'certificate.json').read_text())
    assert n == meta['grid_cells'] == 9408 and d == meta['denominator'] == 52428700000000
    assert F(meta['integral']) == 1 and sha256(raw).hexdigest() == meta['construction_sha256']
    geometry(n)
    controls(root)
    values = all_shifts(a,d)
    maximum = max(values)
    q = score(values,n,d)
    assert q == F(2462273619527794579322422405079,6465103708838880000000000000000) == F(meta['cap'])
    assert maximum == int(meta['integer_peak'])
    assert [k-n for k,v in enumerate(values) if v == maximum] == meta['peak_lags'] == [-2284]
    assert max(values[n:]) < maximum
    false_cap = q-F(2,n*d*d)
    assert any(2*z*false_cap.denominator > n*d*d*false_cap.numerator for z in values)
    assert sha256(''.join(str(z)+'\n' for z in values).encode()).hexdigest() == meta['event_sha256']
    parent = (root/'sources/frontier_parent.txt').read_bytes()
    assert sha256(parent).hexdigest() == meta['parent_sha256'] == '89916aefb6c59e745f1efa224e11f26c663bc5e002384beff15064891caba686'
    pd,*pa = map(int,parent.split())
    previous = score(all_shifts(pa,pd),len(pa),pd)
    assert previous == F(123113681346619,323255185441944) == F(meta['parent_cap'])
    assert previous-q == F(meta['gain']) > 0
    for x,name in [(q,'cap_interval'),(previous-q,'gain_interval')]:
        lo,hi = map(F,meta[name])
        assert lo <= x <= hi and hi-lo <= F(1,10**20)
    print(f'PASS. Direct scan of {len(values)} signed vertices. Only peak at {-2284} bins.')
    print(f'All-event digest {meta["event_sha256"]}. Exact improvement {previous-q}.')
    print('Affine branches, off-grid controls, exterior tails and small-case histograms passed.')

if __name__ == '__main__':
    audit(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent)
