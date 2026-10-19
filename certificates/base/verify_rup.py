#!/usr/bin/env python3
"""Standard-library RUP proof checker; also checks both CNFs encode this graph."""
import pathlib,json,itertools,collections
P=pathlib.Path(__file__).parent;o=json.load(open(P/'certificate.json'));edges=[tuple(e) for e in o['edges']]
def expected(restrained):
 vs=range(1,15) if restrained else range(15);es=[e for e in edges if not restrained or 0 not in e];cls=[]
 for v in vs:
  cls.append(tuple(3*v+c+1 for c in range(3)))
  cls.extend([(-3*v-a-1,-3*v-b-1) for a,b in itertools.combinations(range(3),2)])
 for u,v in es:cls.extend([(-3*u-c-1,-3*v-c-1) for c in range(3)])
 if restrained:cls.extend([(-3*v-c-1,) for v,c in zip(range(1,6),o['f'])])
 return cls
def check(label,restrained):
 cls=[]
 for line in (P/(label+'.cnf')).read_text().splitlines():
  if not line or line[0] in 'cp':continue
  ls=tuple(map(int,line.split()));assert ls[-1]==0;cls.append(ls[:-1])
 canon=lambda rows:collections.Counter(tuple(sorted(c)) for c in rows)
 assert canon(cls)==canon(expected(restrained))
 def contradiction(assumptions):
  ass={}
  for l in assumptions:
   v=abs(l);val=l>0
   if v in ass and ass[v]!=val:return True
   ass[v]=val
  change=True
  while change:
   change=False
   for c in cls:
    if any(abs(l) in ass and ass[abs(l)]==(l>0) for l in c):continue
    rem=[l for l in c if abs(l) not in ass]
    if not rem:return True
    if len(rem)==1:ass[abs(rem[0])]=rem[0]>0;change=True
  return False
 steps=0;empty=False
 for line in (P/(label+'.drup')).read_text().splitlines():
  if not line:continue
  ls=tuple(map(int,line.split()));assert ls[-1]==0;c=ls[:-1]
  assert contradiction([-l for l in c]),('invalid RUP',label,line)
  cls.append(c);steps+=1;empty|=not c
 assert empty
 return steps
print('PASS: exact graph CNFs and RUP refutations verified:',check('ordinary_3color',False),'ordinary steps;',check('restrained_3color',True),'restrained steps.')
