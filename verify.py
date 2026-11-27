"""Offline exact verifier. Run python3 verify.py [certificate-directory]."""
import hashlib
import json
import sys
from fractions import Fraction as F
from pathlib import Path

EXPECTED = F(2462273619527794579322422405079, 6465103708838880000000000000000)
PARENT = F(123113681346619, 323255185441944)
PARENT_HASH = '89916aefb6c59e745f1efa224e11f26c663bc5e002384beff15064891caba686'

def require(ok, why):
    if not ok:
        raise ValueError(why)

def grid_events(a, d):
    n = len(a)
    require(n>0 and type(d) is int and d>0, 'invalid dimensions')
    require(all(type(z) is int and 0<=z<=d for z in a), 'invalid height')
    require(2*sum(a)==n*d, 'mass differs from one')
    width = ((n*d*d).bit_length()+7)//8
    def pack(values):
        return int.from_bytes(b''.join(v.to_bytes(width,'little') for v in values),'little')
    product = pack(a)*pack(d-z for z in reversed(a))
    raw = product.to_bytes((2*n-1)*width,'little')
    return [0]+[int.from_bytes(raw[i:i+width],'little') for i in range(0,len(raw),width)]+[0]

def check_interval(x, texts):
    left,right = map(F,texts)
    require(left <= x <= right and right-left<=F(1,10**20),'invalid decimal enclosure')

def verify(root):
    cert = json.loads((root/'certificate.json').read_text())
    raw = (root/'construction.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==cert['construction_sha256'],'construction hash')
    profile = json.loads(raw)
    a,d = profile['numerators'],profile['denominator']
    n = len(a)
    require((cert['grid_cells'],cert['denominator'])==(n,d),'grid mismatch')
    require(F(cert['integral'])==1,'integral in certificate')
    values = grid_events(a,d)
    peak = max(values)
    cap = F(2*peak,n*d*d)
    lags = [j-n for j,z in enumerate(values) if z==peak]
    require(cap==EXPECTED==F(cert['cap']),'incorrect cap')
    require(peak==int(cert['integer_peak']) and lags==cert['peak_lags'],'incorrect peak or lag')
    digest = hashlib.sha256(''.join(f'{v}\n' for v in values).encode('ascii')).hexdigest()
    require(digest==cert['event_sha256'],'all-event digest')
    source = (root/'sources/frontier_parent.txt').read_bytes()
    require(hashlib.sha256(source).hexdigest()==cert['parent_sha256']==PARENT_HASH,'parent hash')
    pd,*pa = map(int,source.split())
    previous = F(2*max(grid_events(pa,pd)),len(pa)*pd*pd)
    require(previous==PARENT==F(cert['parent_cap']),'parent cap')
    require(previous-cap==F(cert['gain'])>0,'strict improvement')
    check_interval(cap,cert['cap_interval'])
    check_interval(previous-cap,cert['gain_interval'])
    require(cap < F('0.38085601258978320592'), 'advertised strict upper bound')
    require(previous-cap > F('1.14531579911e-9'), 'advertised strict improvement')
    require([F(2*k, n) for k in lags] == [F(-571, 1176)], 'unique physical shift')
    print(f'PASS. {n} cells. Signed vertices {len(values)}. Peaks {lags}.')
    print(f'c <= {cap}. Parent minus cap = {previous-cap}.')

if __name__=='__main__':
    verify(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent)
