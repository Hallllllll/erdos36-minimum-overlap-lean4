"""Emit literals only. All mathematical claims about the literals are proved in Lean."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path


def require(condition, field):
    if not condition:
        raise SystemExit(f"Certificate validation failed: {field}")


root=Path(__file__).resolve().parents[1]
construction = (root / 'construction.json').read_bytes()
cert=json.loads((root/'certificate.json').read_text())
require(hashlib.sha256(construction).hexdigest() == cert['construction_sha256'],
        'construction_sha256')
profile = json.loads(construction)
a=profile['numerators']
d=profile['denominator']
n=len(a)
require(type(d) is int and d > 0 and n >= 64, 'construction dimensions')
require(type(cert['grid_cells']) is int and cert['grid_cells'] == n, 'grid_cells')
require(type(cert['denominator']) is int and cert['denominator'] == d, 'denominator')
require(all(type(x) is int and 0 <= x <= d for x in a), 'construction numerators')
# The n equal cells cover an interval of length 2.
require(Fraction(2 * sum(a), n * d) == Fraction(cert['integral']) == 1, 'integral')
width=((n*d*d).bit_length()+7)//8
def pack(xs):
    return int.from_bytes(b''.join(x.to_bytes(width,'little') for x in xs),'little')
raw=(pack(a)*pack(d-x for x in reversed(a))).to_bytes((2*n-1)*width,'little')
events=[int.from_bytes(raw[i:i+width],'little') for i in range(0,len(raw),width)]
# The packed coefficients cover lags 1 - n through n - 1.
signed_events = [0, *events, 0]
peak = max(signed_events)
peak_lags = [i - n for i, value in enumerate(signed_events) if value == peak]
require(str(peak) == cert['integer_peak'], 'integer_peak')
require(cert['peak_lags'] == peak_lags and all(type(lag) is int for lag in cert['peak_lags']),
        'peak_lags')
require(Fraction(2 * peak, n * d * d) == Fraction(cert['cap']), 'cap')
digest = hashlib.sha256(''.join(f'{x}\n' for x in signed_events).encode('ascii')).hexdigest()
require(digest == cert['event_sha256'], 'event_sha256')
def expr(xs):
    if len(xs)==1: return xs[0]
    k=len(xs)//2
    return f'(Tree.node {expr(xs[:k])} {expr(xs[k:])})'
def tree(out,tag,vs):
    parts=[]
    for i in range(0,len(vs),32):
        ident=f'{tag}_{i//32}'
        parts.append(ident)
        out.append(f'def {ident} : Tree := '+expr([f'(Tree.leaf {x})' for x in vs[i:i+32]]))
    out.append(f'def {tag} : Tree := '+expr(parts))
out=['import Overlap.Tree','namespace Overlap']
tree(out,'heights',a)
tree(out,'events',events)
out+=['end Overlap']
(root/'Overlap/Data.lean').write_text('\n\n'.join(out)+'\n')
small=['import Overlap.Tree','namespace Overlap','set_option maxRecDepth 10000']
sample_start = len(a) // 3
sample = a[sample_start:sample_start + 64]
require(len(sample) == 64 and len(set(sample)) >= 32 and all(0 < x < d for x in sample),
        'nondegenerate benchmark sample')
tree(small, 'sample', sample)
small.append(f'theorem sample_total : sample.total = {sum(sample)} := by decide +kernel')
# Independent direct sums for the 127 signed overlaps of this slice.
s = sample
e=[sum(s[i]*(d-s[i-k]) for i in range(len(s)) if 0<=i-k<len(s)) for k in range(-63,64)]
tree(small,'sampleEvents',e)
small.append(f'theorem sample_product : sample.pack (2^128) * sample.other (2^128) {d} = sampleEvents.pack (2^128) := by decide +kernel')
small+=['#print axioms sample_product','end Overlap']
(root/'Overlap/Bench.lean').write_text('\n\n'.join(small)+'\n')
