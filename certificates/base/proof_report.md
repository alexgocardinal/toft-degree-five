# A 15-vertex counterexample to Toft’s four-critical degree-five question

We exhibit a simple 4-critical graph G, a degree-five vertex x=0, and a nonconstant forbidden-color map f on its five neighbors such that G−x has no proper 3-coloring avoiding f at all five neighbors. This gives a negative answer to the exact question in Jensen and Toft, *Graph Coloring Problems* (1995), Section 5.5, pp. 101–102, attributed there to Toft (1974). The construction and verification are complete. A literature-status audit is still separate: absence of a retrieved prior solution is not a proof of bibliographic novelty.

The graph has 15 vertices, 30 edges, and graph6 encoding:

```
N{e??WOIqAG{?YK_?KG
```

Vertices are 0,…,14. Its adjacency list is:

| Vertex | Neighbors |
|---|---|
| 0 | 1, 2, 3, 4, 5 |
| 1 | 0, 2, 10, 11 |
| 2 | 0, 1, 9, 13 |
| 3 | 0, 4, 8, 13 |
| 4 | 0, 3, 7, 9 |
| 5 | 0, 7, 11 |
| 6 | 9, 11, 13 |
| 7 | 4, 5, 9, 10, 11, 12, 14 |
| 8 | 3, 11, 12, 14 |
| 9 | 2, 4, 6, 7 |
| 10 | 1, 7, 12 |
| 11 | 1, 5, 6, 7, 8 |
| 12 | 7, 8, 10 |
| 13 | 2, 3, 6, 14 |
| 14 | 7, 8, 13 |

The distinguished vertex is x=0, with N(x)={1,2,3,4,5}. Use colors {0,1,2} for 3-colorings, and let

f(1)=f(2)=0, f(3)=f(4)=1, f(5)=2.

## Proof that the graph is not 3-colorable

Suppose G has a proper 3-coloring. Permute colors so vertex 0 has color 0 and vertices 1,2 have colors 1,2, respectively. This is possible because 0,1,2 form a triangle. Since 0,3,4 also form a triangle, vertices 3,4 have colors 1,2 in one order. Vertex 5, adjacent to 0, has color 1 or 2. Thus exactly four cases remain.

In the table, each forced assignment v=c follows because two already colored neighbors of v have the other two colors. The final edge has both ends forced to the same color.

| Colors on vertices 1,2,3,4,5 | Forced colors, in order | Contradictory edge |
|---|---|---|
| 12121 | 7=0, 9=1, 10=2, 11=2, 6=0, 13=0 | 6–13 |
| 12122 | 11=0, 7=1, 8=2, 9=0, 12=0, 10=2, 13=0, 14=0 | 13–14 |
| 12211 | 9=0, 7=2, 10=0, 11=0, 8=1, 12=1 | 8–12 |
| 12212 | 7=0, 9=0 | 7–9 |

All four cases contradict proper coloring. Hence χ(G)≥4.

## Proof that χ(G)=4 and G is 4-critical

The following coloring string records colors on vertices 0,1,…,14, in order:

```
012121000122131
```

Every edge has different endpoint colors, so χ(G)=4. For each edge uv, the table below gives a proper 3-coloring of G−uv. Strings again list colors on vertices 0,…,14. Every proper subgraph of G is 3-colorable: an edge-deleted graph covers every proper subgraph obtained by deleting an edge, and a vertex-deleted graph is contained in an edge-deleted graph incident with the deleted vertex. Thus these witnesses prove full 4-criticality, not merely vertex-criticality.

| Deleted edge | Proper 3-coloring of the remaining graph |
|---|---|
| 0–1 | 110200011202212 |
| 0–2 | 010121000122121 |
| 0–3 | 012011222000110 |
| 0–4 | 012101222100101 |
| 0–5 | 012120110002202 |
| 1–2 | 011122112020020 |
| 1–10 | 012211221010010 |
| 1–11 | 120200011202212 |
| 2–9 | 120022211000212 |
| 2–13 | 012121000122121 |
| 3–4 | 012111122000101 |
| 3–8 | 102022200111212 |
| 3–13 | 012121000122112 |
| 4–7 | 012121122000101 |
| 4–9 | 012211000122112 |
| 5–7 | 012121110002202 |
| 5–11 | 120200221110010 |
| 6–9 | 012121100122101 |
| 6–11 | 012121200122101 |
| 6–13 | 012121000122101 |
| 7–9 | 012121100022101 |
| 7–10 | 210011001202212 |
| 7–11 | 012121202120101 |
| 7–12 | 210011001222012 |
| 7–14 | 120200220101112 |
| 8–11 | 102022201111212 |
| 8–12 | 210011001222112 |
| 8–14 | 102022002121112 |
| 10–12 | 012211221000010 |
| 13–14 | 021211121010000 |

## Proof that no 3-coloring of G−0 avoids f

Suppose φ is such a coloring. The edges 1–2 and 3–4, together with the restrictions, force

(φ(1),φ(2))∈{(1,2),(2,1)}, (φ(3),φ(4))∈{(0,2),(2,0)}, and φ(5)∈{0,1}.

These give exactly eight cases. The same elementary forcing rule gives the following contradictions:

| Colors on vertices 1,2,3,4,5 | Forced colors, in order | Contradictory edge |
|---|---|---|
| 12020 | 7=1, 9=0, 11=2, 6=1, 13=1 | 6–13 |
| 12021 | 7=0, 10=2, 11=2, 8=1, 12=1 | 8–12 |
| 12200 | 9=1, 7=2, 11=2 | 7–11 |
| 12201 | 7=2, 10=0, 11=0, 8=1, 12=1 | 8–12 |
| 21020 | 7=1, 11=1 | 7–11 |
| 21021 | 7=0, 9=0 | 7–9 |
| 21200 | 9=2, 7=1, 11=1 | 7–11 |
| 21201 | 7=2, 9=2 | 7–9 |

Therefore there is no proper 3-coloring φ of G−0 with φ(v)≠f(v) on all five neighbors of 0. The graph, vertex, and map satisfy every hypothesis and violate the requested conclusion.

## Additional exact certificates and bibliographic reference

Up to permutations of the three colors, the complete boundary-coloring relation on (1,2,3,4,5) is exactly

01012, 01020, 01200, 01211.

Every one of these four patterns fails to avoid f under every color permutation. This is supplementary information; the eight-case proof above already proves the required failure.

The accompanying certificate.json contains all 30 edge-deletion and all 15 vertex-deletion colorings. verify_certificate.py checks the explicit colorings and both elementary contradiction tables using only the Python standard library. It requires no SAT solver. ordinary_3color.cnf and restrained_3color.cnf additionally have deletion-free RUP proofs, independently checked by unit propagation; CaDiCaL and a separate backtracking program also verified both UNSAT conclusions.

The problem reference is T. R. Jensen and B. Toft, *Graph Coloring Problems*, Wiley, 1995, §5.5, pp. 101–102; publisher chapter DOI https://doi.org/10.1002/9781118032497.ch5. The cited originating paper is B. Toft, “Color-critical graphs and hypergraphs,” *Journal of Combinatorial Theory, Series B* 16 (1974), 145–161, DOI https://doi.org/10.1016/0095-8956(74)90057-4. The question is 52 years old as of October 2026.
