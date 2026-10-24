import os
import json,numpy as np
from fractions import Fraction as Fr
from gap import diagnostics
from core import s_k
d=json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'cert_ss_fail.json')))
A=np.array([[float(Fr(x)) for x in r] for r in d["A_num"]])
print('s,k',s_k(A))
print(diagnostics(A))
