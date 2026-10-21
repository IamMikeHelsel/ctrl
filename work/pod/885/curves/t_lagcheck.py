import json
from families import pari
from vcheck import analyse
d=json.load(open('poly77_lagrange.json'))
o=analyse(pari(d['C'][1]),pari(d['C'][2])); print(o['nrows'],o.get('maxhit'),o.get('maxtriple'))
