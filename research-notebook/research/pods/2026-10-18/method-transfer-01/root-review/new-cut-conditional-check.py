#!/usr/bin/env python3
"""Exact scalar comparison CONDITIONAL on a stronger, unverified cut bound."""
from fractions import Fraction as Q
import json
I, R, split = Q(1601,40000), Q(2491,100000), Q(493,625)
P=lambda c:(R-I-Q(17,32))*c*c+Q(7,8)*c+R-Q(3,8)
A,B,C=R+Q(1,4)-I,Q(3,8),R+Q(1,8)
margins={'low_cap':R-I*split*split,
 'middle_left':P(split),'middle_right':P(Q(4,5)),
 'middle_concavity':-(R-I-Q(17,32)),
 'upper_leading':A,'upper_discriminant':4*A*C-B*B}
assert Q(3,4)<split<Q(4,5)
assert all(v>0 for v in margins.values())
# A lower bound on total signed weights is not exact normalization.
# This toy only rejects that inference; it does not refute the source LP.
g,weight,floor=Q(-1),Q(2),Q(1)
assert weight>=floor and weight*g<floor*g
print(json.dumps({'status':'exact scalar arithmetic only; stronger graph premise unverified',
 'additional_graph_premise':'every finite triangle-free graph admits a cut with internal cost <= (1601/40000) n^2',
 'result_under_premise':'unchanged completion envelope implies sparse-half cost <= (2491/100000) n^2',
 'I':str(I),'R':str(R),'split':str(split),
 'margins':{k:str(v) for k,v in margins.items()},
 'coverage':'[1/2,split] by cap; [split,4/5] by concavity and endpoint positivity; [4/5,1] by positive quadratic discriminant certificate',
 'source_dependency':'arXiv:2606.28041v1 band envelope and BCL tails; not accepted here',
 'normalization_control':{'g':str(g),'weight':str(weight),'floor':str(floor),'purpose':'per-type weight lower bounds alone do not control signed deficits; inspect actual LP proof'}},indent=2))
