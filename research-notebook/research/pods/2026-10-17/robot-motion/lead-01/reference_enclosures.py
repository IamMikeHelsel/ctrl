"""Rational Bernstein enclosures of the fixed reference streams.

These are sufficient polynomial enclosures, not measured plant outputs.
The generic Bernstein enclosure theorem is established mathematics; this file
checks its finite arithmetic, not a new formal proof of that theorem.
"""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json

HERE=Path(__file__).resolve().parent
spec=json.loads((HERE/"fixed-streams.json").read_text())
checks=json.loads((HERE/"reference-checks.json").read_text())
h=Q(spec["h_s"])

def piece(events,left,right):
    width=right-left
    mid=(left+right)/2
    out=[Q(0)]*5
    for tau,delta in events:
        for i,c in enumerate([1,-4,6,-4,1]):
            root=tau+i*h
            if root < mid:
                for k in range(5):
                    out[k]+=delta*Q(c,24)*comb(4,k)*(left-root)**(4-k)*width**k/h**4
    return out

def differentiated(p,order,width):
    return [p[k+order]*Q(factorial(k+order),factorial(k))/width**order for k in range(len(p)-order)]

def bernstein(p):
    n=len(p)-1
    return [sum(p[k]*Q(comb(i,k),comb(n,k)) for k in range(i+1)) for i in range(n+1)]

rows=[]
for case in checks["cases"]:
    events=[(Q(e["time_s"]),Q(e["delta_m"])) for e in case["accepted_events"]]
    knots=sorted({Q(0)}|{tau+i*h for tau,_ in events for i in range(5)})
    upper={str(i):Q(0) for i in range(5)}
    lower={str(i):Q(0) for i in range(5)}
    cells=[]
    for left,right in zip(knots,knots[1:]):
        p=piece(events,left,right)
        bounds={}
        for order in range(5):
            b=bernstein(differentiated(p,order,right-left))
            lower[str(order)]=min(lower[str(order)],*b)
            upper[str(order)]=max(upper[str(order)],*b)
            bounds[str(order)]={"lower":str(min(b)),"upper":str(max(b)),"coefficients":[str(x) for x in b]}
        cells.append({"left_s":str(left),"right_s":str(right),"bounds":bounds})
    passed=all(max(abs(lower[str(i)]),abs(upper[str(i)]))<=limit for i,limit in [(1,Q(1,10)),(2,Q(1,2)),(3,Q(15,2))])
    rows.append({"case":case["case"],"passed_reference_V_A_J":passed,"global_enclosures":{str(i):{"lower":str(lower[str(i)]),"upper":str(upper[str(i)])} for i in range(5)},"cells":cells})
assert all(row["passed_reference_V_A_J"] for row in rows)
(HERE/"reference-enclosures.json").write_text(json.dumps({"status":"finite rational Bernstein coefficient checks passed; not a physical trajectory certificate","limits":{"velocity_m_s":"1/10","acceleration_m_s2":"1/2","jerk_m_s3":"15/2"},"cases":rows},indent=2)+"\n")
print(json.dumps([{k:v for k,v in row.items() if k!="cells"} for row in rows],indent=2))
