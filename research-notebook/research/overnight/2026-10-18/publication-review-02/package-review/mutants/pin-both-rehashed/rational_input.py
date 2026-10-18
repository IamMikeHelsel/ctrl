"""Exact rational literal generators copied from the independently reviewed client candidate.
Parsing remains outside the Lean theorem. See parser-provenance.json.
"""
from fractions import Fraction
import re

def keys(v,want):
    if not isinstance(v,dict) or set(v)!=set(want): raise ValueError('wrong fields: '+str(want))
def rat(v):
    if not isinstance(v,str) or len(v)>128 or not re.fullmatch(r'-?[0-9]+(?:/[0-9]+)?',v):
        raise ValueError('rationals must be integer or numerator/denominator strings')
    q=Fraction(v)
    return f'({q.numerator}/{q.denominator}:ℚ)'
def version(v):
    if type(v)!=int or v<0: raise ValueError('version must be a nonnegative integer')
    return str(v)
def base(b):
    keys(b,['events','offset','width','version'])
    if not isinstance(b['events'],list): raise ValueError('events must be a list')
    ev=[]
    for e in b['events']:
        if not isinstance(e,list) or len(e)!=2: raise ValueError('an event has time and increment')
        ev.append('('+rat(e[0])+','+rat(e[1])+')')
    return '⟨['+','.join(ev)+'],'+rat(b['offset'])+','+rat(b['width'])+','+version(b['version'])+'⟩'
def task(t):
    fields=['goal','request','deadline','speed','accel','jerkLimit','version'];keys(t,fields)
    return '⟨'+','.join([rat(t[k]) for k in fields[:-1]]+[version(t['version'])])+'⟩'
def timing(t):
    fields=['completion','commitTime','dispatch'];keys(t,fields)
    return '⟨'+','.join(rat(t[k]) for k in fields)+'⟩'
def pending(p):
    keys(p,['base','task','execution','delta','candidates'])
    if not isinstance(p['candidates'],list): raise ValueError('candidates must be a list')
    return '⟨'+','.join([base(p['base']),task(p['task']),rat(p['execution']),rat(p['delta']),
        '['+','.join(rat(x) for x in p['candidates'])+']'])+'⟩'
