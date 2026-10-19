#!/usr/bin/env python3
"""Verify the Toft counterexample with only Python's standard library.
Checks all positive coloring witnesses and complete elementary contradiction
case splits. No external packages, SAT solver, or trusted solver result needed.
"""
import json,pathlib,itertools
P=pathlib.Path(__file__).parent;o=json.load(open(P/'certificate.json'));t=json.load(open(P/'human_traces.json'))
n=o['n'];edges={tuple(e) for e in o['edges']};assert n==15 and len(edges)==30
assert all(0<=u<v<n for u,v in edges)
adj={v:set() for v in range(n)}
for u,v in edges:adj[u].add(v);adj[v].add(u)
assert sorted(adj[0])==[1,2,3,4,5]
assert o['f']==[0,0,1,1,2]
assert {int(v):set(ns) for v,ns in o['adjacency'].items()}==adj

def check_coloring(c,k,delete_edge=None,delete_vertex=None):
 c={int(v):col for v,col in c.items()};assert set(c)==set(range(n))-({delete_vertex} if delete_vertex is not None else set())
 assert all(col in range(k) for col in c.values())
 for u,v in edges:
  if delete_edge is not None and (u,v)==tuple(delete_edge):continue
  if delete_vertex in (u,v):continue
  assert c[u]!=c[v],(u,v,c)
check_coloring(o['four_coloring'],4)
assert {tuple(w['deleted']) for w in o['edge_deletion_three_colorings']}==edges
for w in o['edge_deletion_three_colorings']:check_coloring(w['color'],3,delete_edge=w['deleted'])
assert {w['deleted'] for w in o['vertex_deletion_three_colorings']}==set(range(n))
for w in o['vertex_deletion_three_colorings']:check_coloring(w['color'],3,delete_vertex=w['deleted'])
ordinary={(1,2,a,b,e) for a,b in [(1,2),(2,1)] for e in [1,2]}
restrained={(a,b,c,d,e) for a,b in [(1,2),(2,1)] for c,d in [(0,2),(2,0)] for e in [0,1]}
assert {tuple(row[0]) for row in t['ordinary']}==ordinary
assert {tuple(row[0]) for row in t['restrained']}==restrained
for mode in ['ordinary','restrained']:
 for nb,seq,conf in t[mode]:
  c={i+1:color for i,color in enumerate(nb)}
  if mode=='ordinary':c[0]=0
  for v,color in seq:
   assert v not in c and color in range(3)
   known={c[w] for w in adj[v] if w in c}
   assert set(range(3))-{color}<=known,(mode,nb,v,color,known)
   c[v]=color
  a,b=conf;assert tuple(sorted((a,b))) in edges and c[a]==c[b],(mode,nb,conf)
print('PASS: simple15vertex30edgegraph; degree-five0; χ=4; all30edge and15vertex deletion witnesses; all4ordinary and8restrained contradiction cases. No solver used.')
