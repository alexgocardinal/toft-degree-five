import Lean

namespace ToftDegreeFive

def edges : List (Nat × Nat) :=
  [(0,1), (0,2), (0,3), (0,4), (0,5),
   (1,2), (1,10), (1,11), (2,9), (2,13),
   (3,4), (3,8), (3,13), (4,7), (4,9),
   (5,7), (5,11), (6,9), (6,11), (6,13),
   (7,9), (7,10), (7,11), (7,12), (7,14),
   (8,11), (8,12), (8,14), (10,12), (13,14)]

def Adj (u v : Nat) : Prop :=
  (u,v) ∈ edges ∨ (v,u) ∈ edges

instance (u v : Nat) : Decidable (Adj u v) :=
  inferInstanceAs (Decidable ((u,v) ∈ edges ∨ (v,u) ∈ edges))

def Proper (c : Nat → Nat) : Prop :=
  ∀ e ∈ edges, c e.1 ≠ c e.2

def fourColor (v : Nat) : Nat :=
  ([0,1,2,1,2,1,0,0,0,1,2,2,1,3,1] : List Nat).getD v 0

theorem edge_count : edges.length = 30 := by decide

theorem edges_valid :
    ∀ e ∈ edges, e.1 < e.2 ∧ e.2 < 15 := by decide

theorem edges_distinct : edges.Nodup := by decide

theorem zero_neighbors (v : Nat) :
    Adj 0 v ↔ v ∈ ([1,2,3,4,5] : List Nat) := by
  simp [Adj, edges]

theorem fourColor_proper : Proper fourColor := by
  unfold Proper
  decide

theorem fourColor_bound :
    ∀ v ∈ List.range 15, fourColor v < 4 := by decide

#print axioms fourColor_proper
#print axioms zero_neighbors

end ToftDegreeFive

namespace ToftDegreeFive

set_option maxHeartbeats 2000000

def ProperWithoutZero (c : Nat → Nat) : Prop :=
  ∀ e ∈ edges, e.1 ≠ 0 → c e.1 ≠ c e.2


private theorem pair12 (a b : Nat)
    (ha : a < 3) (hb : b < 3)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by omega

private theorem pair02 (a b : Nat)
    (ha : a < 3) (hb : b < 3)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by omega

private theorem color01 (a : Nat)
    (ha : a < 3) (ha2 : a ≠ 2) :
    a = 0 ∨ a = 1 := by omega

private theorem force0 (a : Nat)
    (ha : a < 3) (h1 : a ≠ 1) (h2 : a ≠ 2) :
    a = 0 := by omega

private theorem force1 (a : Nat)
    (ha : a < 3) (h0 : a ≠ 0) (h2 : a ≠ 2) :
    a = 1 := by omega

private theorem force2 (a : Nat)
    (ha : a < 3) (h0 : a ≠ 0) (h1 : a ≠ 1) :
    a = 2 := by omega

theorem no_avoiding_coloring (c : Nat → Nat)
    (hc : ∀ v, v < 15 → v ≠ 0 → c v < 3)
    (hp : ProperWithoutZero c)
    (hf1 : c 1 ≠ 0) (hf2 : c 2 ≠ 0)
    (hf3 : c 3 ≠ 1) (hf4 : c 4 ≠ 1)
    (hf5 : c 5 ≠ 2) : False := by
  have b1 := hc 1 (by decide) (by decide)
  have b2 := hc 2 (by decide) (by decide)
  have b3 := hc 3 (by decide) (by decide)
  have b4 := hc 4 (by decide) (by decide)
  have b5 := hc 5 (by decide) (by decide)
  have b6 := hc 6 (by decide) (by decide)
  have b7 := hc 7 (by decide) (by decide)
  have b8 := hc 8 (by decide) (by decide)
  have b9 := hc 9 (by decide) (by decide)
  have b10 := hc 10 (by decide) (by decide)
  have b11 := hc 11 (by decide) (by decide)
  have b12 := hc 12 (by decide) (by decide)
  have b13 := hc 13 (by decide) (by decide)
  have b14 := hc 14 (by decide) (by decide)
  have e1_2 := hp (1,2) (by decide) (by decide)
  have e1_10 := hp (1,10) (by decide) (by decide)
  have e1_11 := hp (1,11) (by decide) (by decide)
  have e2_9 := hp (2,9) (by decide) (by decide)
  have e2_13 := hp (2,13) (by decide) (by decide)
  have e3_4 := hp (3,4) (by decide) (by decide)
  have e3_8 := hp (3,8) (by decide) (by decide)
  have e3_13 := hp (3,13) (by decide) (by decide)
  have e4_7 := hp (4,7) (by decide) (by decide)
  have e4_9 := hp (4,9) (by decide) (by decide)
  have e5_7 := hp (5,7) (by decide) (by decide)
  have e5_11 := hp (5,11) (by decide) (by decide)
  have e6_9 := hp (6,9) (by decide) (by decide)
  have e6_11 := hp (6,11) (by decide) (by decide)
  have e6_13 := hp (6,13) (by decide) (by decide)
  have e7_9 := hp (7,9) (by decide) (by decide)
  have e7_10 := hp (7,10) (by decide) (by decide)
  have e7_11 := hp (7,11) (by decide) (by decide)
  have e7_12 := hp (7,12) (by decide) (by decide)
  have e7_14 := hp (7,14) (by decide) (by decide)
  have e8_11 := hp (8,11) (by decide) (by decide)
  have e8_12 := hp (8,12) (by decide) (by decide)
  have e8_14 := hp (8,14) (by decide) (by decide)
  have e10_12 := hp (10,12) (by decide) (by decide)
  have e13_14 := hp (13,14) (by decide) (by decide)
  have hb12 := pair12 (c 1) (c 2) b1 b2 hf1 hf2 e1_2
  have hb34 := pair02 (c 3) (c 4) b3 b4 hf3 hf4 e3_4
  have hb5 := color01 (c 5) b5 hf5
  rcases hb12 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hb34 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases hb5 with h5 | h5
  · -- Boundary colors: 12020
    have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
    have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h7] using (Ne.symm e7_9)) (by simpa only [h2] using (Ne.symm e2_9))
    have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h5] using (Ne.symm e5_11)) (by simpa only [h1] using (Ne.symm e1_11))
    have h6 : c 6 = 1 := force1 (c 6) b6 (by simpa only [h9] using e6_9) (by simpa only [h11] using e6_11)
    have h13 : c 13 = 1 := force1 (c 13) b13 (by simpa only [h3] using (Ne.symm e3_13)) (by simpa only [h2] using (Ne.symm e2_13))
    exact e6_13 (h6.trans h13.symm)
  · -- Boundary colors: 12021
    have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
    have h10 : c 10 = 2 := force2 (c 10) b10 (by simpa only [h7] using (Ne.symm e7_10)) (by simpa only [h1] using (Ne.symm e1_10))
    have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h7] using (Ne.symm e7_11)) (by simpa only [h1] using (Ne.symm e1_11))
    have h8 : c 8 = 1 := force1 (c 8) b8 (by simpa only [h3] using (Ne.symm e3_8)) (by simpa only [h11] using e8_11)
    have h12 : c 12 = 1 := force1 (c 12) b12 (by simpa only [h7] using (Ne.symm e7_12)) (by simpa only [h10] using (Ne.symm e10_12))
    exact e8_12 (h8.trans h12.symm)
  · -- Boundary colors: 12200
    have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
    have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h9] using e7_9)
    have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h5] using (Ne.symm e5_11)) (by simpa only [h1] using (Ne.symm e1_11))
    exact e7_11 (h7.trans h11.symm)
  · -- Boundary colors: 12201
    have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h5] using (Ne.symm e5_7))
    have h10 : c 10 = 0 := force0 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h7] using (Ne.symm e7_10))
    have h11 : c 11 = 0 := force0 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h7] using (Ne.symm e7_11))
    have h8 : c 8 = 1 := force1 (c 8) b8 (by simpa only [h11] using e8_11) (by simpa only [h3] using (Ne.symm e3_8))
    have h12 : c 12 = 1 := force1 (c 12) b12 (by simpa only [h10] using (Ne.symm e10_12)) (by simpa only [h7] using (Ne.symm e7_12))
    exact e8_12 (h8.trans h12.symm)
  · -- Boundary colors: 21020
    have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
    have h11 : c 11 = 1 := force1 (c 11) b11 (by simpa only [h5] using (Ne.symm e5_11)) (by simpa only [h1] using (Ne.symm e1_11))
    exact e7_11 (h7.trans h11.symm)
  · -- Boundary colors: 21021
    have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
    have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h4] using (Ne.symm e4_9))
    exact e7_9 (h7.trans h9.symm)
  · -- Boundary colors: 21200
    have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
    have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h9] using e7_9)
    have h11 : c 11 = 1 := force1 (c 11) b11 (by simpa only [h5] using (Ne.symm e5_11)) (by simpa only [h1] using (Ne.symm e1_11))
    exact e7_11 (h7.trans h11.symm)
  · -- Boundary colors: 21201
    have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h5] using (Ne.symm e5_7))
    have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
    exact e7_9 (h7.trans h9.symm)

#print axioms no_avoiding_coloring

end ToftDegreeFive


namespace ToftDegreeFive

def edgeWitnesses : List ((Nat × Nat) × List Nat) :=
  edges.zip
  [[1,1,0,2,0,0,0,1,1,2,0,2,2,1,2],
   [0,1,0,1,2,1,0,0,0,1,2,2,1,2,1],
   [0,1,2,0,1,1,2,2,2,0,0,0,1,1,0],
   [0,1,2,1,0,1,2,2,2,1,0,0,1,0,1],
   [0,1,2,1,2,0,1,1,0,0,0,2,2,0,2],
   [0,1,1,1,2,2,1,1,2,0,2,0,0,2,0],
   [0,1,2,2,1,1,2,2,1,0,1,0,0,1,0],
   [1,2,0,2,0,0,0,1,1,2,0,2,2,1,2],
   [1,2,0,0,2,2,2,1,1,0,0,0,2,1,2],
   [0,1,2,1,2,1,0,0,0,1,2,2,1,2,1],
   [0,1,2,1,1,1,1,2,2,0,0,0,1,0,1],
   [1,0,2,0,2,2,2,0,0,1,1,1,2,1,2],
   [0,1,2,1,2,1,0,0,0,1,2,2,1,1,2],
   [0,1,2,1,2,1,1,2,2,0,0,0,1,0,1],
   [0,1,2,2,1,1,0,0,0,1,2,2,1,1,2],
   [0,1,2,1,2,1,1,1,0,0,0,2,2,0,2],
   [1,2,0,2,0,0,2,2,1,1,1,0,0,1,0],
   [0,1,2,1,2,1,1,0,0,1,2,2,1,0,1],
   [0,1,2,1,2,1,2,0,0,1,2,2,1,0,1],
   [0,1,2,1,2,1,0,0,0,1,2,2,1,0,1],
   [0,1,2,1,2,1,1,0,0,0,2,2,1,0,1],
   [2,1,0,0,1,1,0,0,1,2,0,2,2,1,2],
   [0,1,2,1,2,1,2,0,2,1,2,0,1,0,1],
   [2,1,0,0,1,1,0,0,1,2,2,2,0,1,2],
   [1,2,0,2,0,0,2,2,0,1,0,1,1,1,2],
   [1,0,2,0,2,2,2,0,1,1,1,1,2,1,2],
   [2,1,0,0,1,1,0,0,1,2,2,2,1,1,2],
   [1,0,2,0,2,2,0,0,2,1,2,1,1,1,2],
   [0,1,2,2,1,1,2,2,1,0,0,0,0,1,0],
   [0,2,1,2,1,1,1,2,1,0,1,0,0,0,0]]

theorem edgeWitnesses_cover :
    edgeWitnesses.map Prod.fst = edges := by decide

theorem edgeWitnesses_valid :
    ∀ w ∈ edgeWitnesses,
      (∀ v ∈ List.range 15, w.2.getD v 0 < 3) ∧
      (∀ e ∈ edges, e ≠ w.1 →
        w.2.getD e.1 0 ≠ w.2.getD e.2 0) := by
  decide

#print axioms edgeWitnesses_cover
#print axioms edgeWitnesses_valid

end ToftDegreeFive


namespace ToftDegreeFive

private theorem color_cases (a : Nat) (ha : a < 3) :
    a = 0 ∨ a = 1 ∨ a = 2 := by omega

private theorem pair01 (a b : Nat)
    (ha : a < 3) (hb : b < 3)
    (ha2 : a ≠ 2) (hb2 : b ≠ 2) (hab : a ≠ b) :
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega

private theorem color12 (a : Nat)
    (ha : a < 3) (ha0 : a ≠ 0) :
    a = 1 ∨ a = 2 := by omega

private theorem color02 (a : Nat)
    (ha : a < 3) (ha1 : a ≠ 1) :
    a = 0 ∨ a = 2 := by omega

theorem not_three_colorable (c : Nat → Nat)
    (hc : ∀ v, v < 15 → c v < 3)
    (hp : Proper c) : False := by
  have b0 := hc 0 (by decide)
  have b1 := hc 1 (by decide)
  have b2 := hc 2 (by decide)
  have b3 := hc 3 (by decide)
  have b4 := hc 4 (by decide)
  have b5 := hc 5 (by decide)
  have b6 := hc 6 (by decide)
  have b7 := hc 7 (by decide)
  have b8 := hc 8 (by decide)
  have b9 := hc 9 (by decide)
  have b10 := hc 10 (by decide)
  have b11 := hc 11 (by decide)
  have b12 := hc 12 (by decide)
  have b13 := hc 13 (by decide)
  have b14 := hc 14 (by decide)
  have e0_1 := hp (0,1) (by decide)
  have e0_2 := hp (0,2) (by decide)
  have e0_3 := hp (0,3) (by decide)
  have e0_4 := hp (0,4) (by decide)
  have e0_5 := hp (0,5) (by decide)
  have e1_2 := hp (1,2) (by decide)
  have e1_10 := hp (1,10) (by decide)
  have e1_11 := hp (1,11) (by decide)
  have e2_9 := hp (2,9) (by decide)
  have e2_13 := hp (2,13) (by decide)
  have e3_4 := hp (3,4) (by decide)
  have e3_8 := hp (3,8) (by decide)
  have e3_13 := hp (3,13) (by decide)
  have e4_7 := hp (4,7) (by decide)
  have e4_9 := hp (4,9) (by decide)
  have e5_7 := hp (5,7) (by decide)
  have e5_11 := hp (5,11) (by decide)
  have e6_9 := hp (6,9) (by decide)
  have e6_11 := hp (6,11) (by decide)
  have e6_13 := hp (6,13) (by decide)
  have e7_9 := hp (7,9) (by decide)
  have e7_10 := hp (7,10) (by decide)
  have e7_11 := hp (7,11) (by decide)
  have e7_12 := hp (7,12) (by decide)
  have e7_14 := hp (7,14) (by decide)
  have e8_11 := hp (8,11) (by decide)
  have e8_12 := hp (8,12) (by decide)
  have e8_14 := hp (8,14) (by decide)
  have e10_12 := hp (10,12) (by decide)
  have e13_14 := hp (13,14) (by decide)
  rcases color_cases (c 0) b0 with h0 | h0 | h0
  · have hb12 := pair12 (c 1) (c 2) b1 b2 (by simpa only [h0] using (Ne.symm e0_1)) (by simpa only [h0] using (Ne.symm e0_2)) e1_2
    have hb34 := pair12 (c 3) (c 4) b3 b4 (by simpa only [h0] using (Ne.symm e0_3)) (by simpa only [h0] using (Ne.symm e0_4)) e3_4
    have hb5 := color12 (c 5) b5 (by simpa only [h0] using (Ne.symm e0_5))
    rcases hb12 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hb34 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases hb5 with h5 | h5
    ·
      have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
      have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h7] using (Ne.symm e7_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h10 : c 10 = 2 := force2 (c 10) b10 (by simpa only [h7] using (Ne.symm e7_10)) (by simpa only [h1] using (Ne.symm e1_10))
      have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h7] using (Ne.symm e7_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h6 : c 6 = 0 := force0 (c 6) b6 (by simpa only [h9] using e6_9) (by simpa only [h11] using e6_11)
      have h13 : c 13 = 0 := force0 (c 13) b13 (by simpa only [h3] using (Ne.symm e3_13)) (by simpa only [h2] using (Ne.symm e2_13))
      exact e6_13 (h6.trans h13.symm)
    ·
      have h11 : c 11 = 0 := force0 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h5] using (Ne.symm e5_11))
      have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h11] using e7_11) (by simpa only [h4] using (Ne.symm e4_7))
      have h8 : c 8 = 2 := force2 (c 8) b8 (by simpa only [h11] using e8_11) (by simpa only [h3] using (Ne.symm e3_8))
      have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h7] using (Ne.symm e7_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h12 : c 12 = 0 := force0 (c 12) b12 (by simpa only [h7] using (Ne.symm e7_12)) (by simpa only [h8] using (Ne.symm e8_12))
      have h10 : c 10 = 2 := force2 (c 10) b10 (by simpa only [h12] using e10_12) (by simpa only [h1] using (Ne.symm e1_10))
      have h13 : c 13 = 0 := force0 (c 13) b13 (by simpa only [h3] using (Ne.symm e3_13)) (by simpa only [h2] using (Ne.symm e2_13))
      have h14 : c 14 = 0 := force0 (c 14) b14 (by simpa only [h7] using (Ne.symm e7_14)) (by simpa only [h8] using (Ne.symm e8_14))
      exact e13_14 (h13.trans h14.symm)
    ·
      have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h9] using e7_9) (by simpa only [h4] using (Ne.symm e4_7))
      have h10 : c 10 = 0 := force0 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h7] using (Ne.symm e7_10))
      have h11 : c 11 = 0 := force0 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h7] using (Ne.symm e7_11))
      have h8 : c 8 = 1 := force1 (c 8) b8 (by simpa only [h11] using e8_11) (by simpa only [h3] using (Ne.symm e3_8))
      have h12 : c 12 = 1 := force1 (c 12) b12 (by simpa only [h10] using (Ne.symm e10_12)) (by simpa only [h7] using (Ne.symm e7_12))
      exact e8_12 (h8.trans h12.symm)
    ·
      have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h5] using (Ne.symm e5_7))
      have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
      exact e7_9 (h7.trans h9.symm)
    ·
      have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
      have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h4] using (Ne.symm e4_9))
      exact e7_9 (h7.trans h9.symm)
    ·
      have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h4] using (Ne.symm e4_9))
      have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h9] using e7_9) (by simpa only [h4] using (Ne.symm e4_7))
      have h10 : c 10 = 0 := force0 (c 10) b10 (by simpa only [h7] using (Ne.symm e7_10)) (by simpa only [h1] using (Ne.symm e1_10))
      have h11 : c 11 = 0 := force0 (c 11) b11 (by simpa only [h7] using (Ne.symm e7_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h8 : c 8 = 2 := force2 (c 8) b8 (by simpa only [h11] using e8_11) (by simpa only [h3] using (Ne.symm e3_8))
      have h12 : c 12 = 2 := force2 (c 12) b12 (by simpa only [h10] using (Ne.symm e10_12)) (by simpa only [h7] using (Ne.symm e7_12))
      exact e8_12 (h8.trans h12.symm)
    ·
      have h11 : c 11 = 0 := force0 (c 11) b11 (by simpa only [h5] using (Ne.symm e5_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h11] using e7_11) (by simpa only [h4] using (Ne.symm e4_7))
      have h8 : c 8 = 1 := force1 (c 8) b8 (by simpa only [h11] using e8_11) (by simpa only [h3] using (Ne.symm e3_8))
      have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h7] using (Ne.symm e7_9))
      have h12 : c 12 = 0 := force0 (c 12) b12 (by simpa only [h8] using (Ne.symm e8_12)) (by simpa only [h7] using (Ne.symm e7_12))
      have h10 : c 10 = 1 := force1 (c 10) b10 (by simpa only [h12] using e10_12) (by simpa only [h1] using (Ne.symm e1_10))
      have h13 : c 13 = 0 := force0 (c 13) b13 (by simpa only [h2] using (Ne.symm e2_13)) (by simpa only [h3] using (Ne.symm e3_13))
      have h14 : c 14 = 0 := force0 (c 14) b14 (by simpa only [h8] using (Ne.symm e8_14)) (by simpa only [h7] using (Ne.symm e7_14))
      exact e13_14 (h13.trans h14.symm)
    ·
      have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h5] using (Ne.symm e5_7))
      have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h7] using (Ne.symm e7_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h10 : c 10 = 1 := force1 (c 10) b10 (by simpa only [h7] using (Ne.symm e7_10)) (by simpa only [h1] using (Ne.symm e1_10))
      have h11 : c 11 = 1 := force1 (c 11) b11 (by simpa only [h7] using (Ne.symm e7_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h6 : c 6 = 0 := force0 (c 6) b6 (by simpa only [h11] using e6_11) (by simpa only [h9] using e6_9)
      have h13 : c 13 = 0 := force0 (c 13) b13 (by simpa only [h2] using (Ne.symm e2_13)) (by simpa only [h3] using (Ne.symm e3_13))
      exact e6_13 (h6.trans h13.symm)
  · have hb12 := pair02 (c 1) (c 2) b1 b2 (by simpa only [h0] using (Ne.symm e0_1)) (by simpa only [h0] using (Ne.symm e0_2)) e1_2
    have hb34 := pair02 (c 3) (c 4) b3 b4 (by simpa only [h0] using (Ne.symm e0_3)) (by simpa only [h0] using (Ne.symm e0_4)) e3_4
    have hb5 := color02 (c 5) b5 (by simpa only [h0] using (Ne.symm e0_5))
    rcases hb12 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hb34 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases hb5 with h5 | h5
    ·
      have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
      have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h7] using (Ne.symm e7_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h10 : c 10 = 2 := force2 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h7] using (Ne.symm e7_10))
      have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h7] using (Ne.symm e7_11))
      have h6 : c 6 = 1 := force1 (c 6) b6 (by simpa only [h9] using e6_9) (by simpa only [h11] using e6_11)
      have h13 : c 13 = 1 := force1 (c 13) b13 (by simpa only [h3] using (Ne.symm e3_13)) (by simpa only [h2] using (Ne.symm e2_13))
      exact e6_13 (h6.trans h13.symm)
    ·
      have h11 : c 11 = 1 := force1 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h5] using (Ne.symm e5_11))
      have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h11] using e7_11) (by simpa only [h4] using (Ne.symm e4_7))
      have h8 : c 8 = 2 := force2 (c 8) b8 (by simpa only [h3] using (Ne.symm e3_8)) (by simpa only [h11] using e8_11)
      have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h7] using (Ne.symm e7_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h12 : c 12 = 1 := force1 (c 12) b12 (by simpa only [h7] using (Ne.symm e7_12)) (by simpa only [h8] using (Ne.symm e8_12))
      have h10 : c 10 = 2 := force2 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h12] using e10_12)
      have h13 : c 13 = 1 := force1 (c 13) b13 (by simpa only [h3] using (Ne.symm e3_13)) (by simpa only [h2] using (Ne.symm e2_13))
      have h14 : c 14 = 1 := force1 (c 14) b14 (by simpa only [h7] using (Ne.symm e7_14)) (by simpa only [h8] using (Ne.symm e8_14))
      exact e13_14 (h13.trans h14.symm)
    ·
      have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h9] using e7_9)
      have h10 : c 10 = 1 := force1 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h7] using (Ne.symm e7_10))
      have h11 : c 11 = 1 := force1 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h7] using (Ne.symm e7_11))
      have h8 : c 8 = 0 := force0 (c 8) b8 (by simpa only [h11] using e8_11) (by simpa only [h3] using (Ne.symm e3_8))
      have h12 : c 12 = 0 := force0 (c 12) b12 (by simpa only [h10] using (Ne.symm e10_12)) (by simpa only [h7] using (Ne.symm e7_12))
      exact e8_12 (h8.trans h12.symm)
    ·
      have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h5] using (Ne.symm e5_7))
      have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
      exact e7_9 (h7.trans h9.symm)
    ·
      have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
      have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h4] using (Ne.symm e4_9))
      exact e7_9 (h7.trans h9.symm)
    ·
      have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h4] using (Ne.symm e4_9))
      have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h9] using e7_9) (by simpa only [h4] using (Ne.symm e4_7))
      have h10 : c 10 = 1 := force1 (c 10) b10 (by simpa only [h7] using (Ne.symm e7_10)) (by simpa only [h1] using (Ne.symm e1_10))
      have h11 : c 11 = 1 := force1 (c 11) b11 (by simpa only [h7] using (Ne.symm e7_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h8 : c 8 = 2 := force2 (c 8) b8 (by simpa only [h3] using (Ne.symm e3_8)) (by simpa only [h11] using e8_11)
      have h12 : c 12 = 2 := force2 (c 12) b12 (by simpa only [h7] using (Ne.symm e7_12)) (by simpa only [h10] using (Ne.symm e10_12))
      exact e8_12 (h8.trans h12.symm)
    ·
      have h11 : c 11 = 1 := force1 (c 11) b11 (by simpa only [h5] using (Ne.symm e5_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h11] using e7_11)
      have h8 : c 8 = 0 := force0 (c 8) b8 (by simpa only [h11] using e8_11) (by simpa only [h3] using (Ne.symm e3_8))
      have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h7] using (Ne.symm e7_9))
      have h12 : c 12 = 1 := force1 (c 12) b12 (by simpa only [h8] using (Ne.symm e8_12)) (by simpa only [h7] using (Ne.symm e7_12))
      have h10 : c 10 = 0 := force0 (c 10) b10 (by simpa only [h12] using e10_12) (by simpa only [h1] using (Ne.symm e1_10))
      have h13 : c 13 = 1 := force1 (c 13) b13 (by simpa only [h2] using (Ne.symm e2_13)) (by simpa only [h3] using (Ne.symm e3_13))
      have h14 : c 14 = 1 := force1 (c 14) b14 (by simpa only [h8] using (Ne.symm e8_14)) (by simpa only [h7] using (Ne.symm e7_14))
      exact e13_14 (h13.trans h14.symm)
    ·
      have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h5] using (Ne.symm e5_7))
      have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h7] using (Ne.symm e7_9))
      have h10 : c 10 = 0 := force0 (c 10) b10 (by simpa only [h7] using (Ne.symm e7_10)) (by simpa only [h1] using (Ne.symm e1_10))
      have h11 : c 11 = 0 := force0 (c 11) b11 (by simpa only [h7] using (Ne.symm e7_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h6 : c 6 = 1 := force1 (c 6) b6 (by simpa only [h11] using e6_11) (by simpa only [h9] using e6_9)
      have h13 : c 13 = 1 := force1 (c 13) b13 (by simpa only [h2] using (Ne.symm e2_13)) (by simpa only [h3] using (Ne.symm e3_13))
      exact e6_13 (h6.trans h13.symm)
  · have hb12 := pair01 (c 1) (c 2) b1 b2 (by simpa only [h0] using (Ne.symm e0_1)) (by simpa only [h0] using (Ne.symm e0_2)) e1_2
    have hb34 := pair01 (c 3) (c 4) b3 b4 (by simpa only [h0] using (Ne.symm e0_3)) (by simpa only [h0] using (Ne.symm e0_4)) e3_4
    have hb5 := color01 (c 5) b5 (by simpa only [h0] using (Ne.symm e0_5))
    rcases hb12 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases hb34 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rcases hb5 with h5 | h5
    ·
      have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
      have h9 : c 9 = 0 := force0 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h7] using (Ne.symm e7_9))
      have h10 : c 10 = 1 := force1 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h7] using (Ne.symm e7_10))
      have h11 : c 11 = 1 := force1 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h7] using (Ne.symm e7_11))
      have h6 : c 6 = 2 := force2 (c 6) b6 (by simpa only [h9] using e6_9) (by simpa only [h11] using e6_11)
      have h13 : c 13 = 2 := force2 (c 13) b13 (by simpa only [h3] using (Ne.symm e3_13)) (by simpa only [h2] using (Ne.symm e2_13))
      exact e6_13 (h6.trans h13.symm)
    ·
      have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h5] using (Ne.symm e5_11))
      have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h11] using e7_11)
      have h8 : c 8 = 1 := force1 (c 8) b8 (by simpa only [h3] using (Ne.symm e3_8)) (by simpa only [h11] using e8_11)
      have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h7] using (Ne.symm e7_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h12 : c 12 = 2 := force2 (c 12) b12 (by simpa only [h7] using (Ne.symm e7_12)) (by simpa only [h8] using (Ne.symm e8_12))
      have h10 : c 10 = 1 := force1 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h12] using e10_12)
      have h13 : c 13 = 2 := force2 (c 13) b13 (by simpa only [h3] using (Ne.symm e3_13)) (by simpa only [h2] using (Ne.symm e2_13))
      have h14 : c 14 = 2 := force2 (c 14) b14 (by simpa only [h7] using (Ne.symm e7_14)) (by simpa only [h8] using (Ne.symm e8_14))
      exact e13_14 (h13.trans h14.symm)
    ·
      have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
      have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h9] using e7_9)
      have h10 : c 10 = 2 := force2 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h7] using (Ne.symm e7_10))
      have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h7] using (Ne.symm e7_11))
      have h8 : c 8 = 0 := force0 (c 8) b8 (by simpa only [h3] using (Ne.symm e3_8)) (by simpa only [h11] using e8_11)
      have h12 : c 12 = 0 := force0 (c 12) b12 (by simpa only [h7] using (Ne.symm e7_12)) (by simpa only [h10] using (Ne.symm e10_12))
      exact e8_12 (h8.trans h12.symm)
    ·
      have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h5] using (Ne.symm e5_7))
      have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h4] using (Ne.symm e4_9)) (by simpa only [h2] using (Ne.symm e2_9))
      exact e7_9 (h7.trans h9.symm)
    ·
      have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h5] using (Ne.symm e5_7)) (by simpa only [h4] using (Ne.symm e4_7))
      have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h4] using (Ne.symm e4_9))
      exact e7_9 (h7.trans h9.symm)
    ·
      have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h4] using (Ne.symm e4_9))
      have h7 : c 7 = 0 := force0 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h9] using e7_9)
      have h10 : c 10 = 2 := force2 (c 10) b10 (by simpa only [h7] using (Ne.symm e7_10)) (by simpa only [h1] using (Ne.symm e1_10))
      have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h7] using (Ne.symm e7_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h8 : c 8 = 1 := force1 (c 8) b8 (by simpa only [h3] using (Ne.symm e3_8)) (by simpa only [h11] using e8_11)
      have h12 : c 12 = 1 := force1 (c 12) b12 (by simpa only [h7] using (Ne.symm e7_12)) (by simpa only [h10] using (Ne.symm e10_12))
      exact e8_12 (h8.trans h12.symm)
    ·
      have h11 : c 11 = 2 := force2 (c 11) b11 (by simpa only [h5] using (Ne.symm e5_11)) (by simpa only [h1] using (Ne.symm e1_11))
      have h7 : c 7 = 1 := force1 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h11] using e7_11)
      have h8 : c 8 = 0 := force0 (c 8) b8 (by simpa only [h3] using (Ne.symm e3_8)) (by simpa only [h11] using e8_11)
      have h9 : c 9 = 2 := force2 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h7] using (Ne.symm e7_9))
      have h12 : c 12 = 2 := force2 (c 12) b12 (by simpa only [h8] using (Ne.symm e8_12)) (by simpa only [h7] using (Ne.symm e7_12))
      have h10 : c 10 = 0 := force0 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h12] using e10_12)
      have h13 : c 13 = 2 := force2 (c 13) b13 (by simpa only [h2] using (Ne.symm e2_13)) (by simpa only [h3] using (Ne.symm e3_13))
      have h14 : c 14 = 2 := force2 (c 14) b14 (by simpa only [h8] using (Ne.symm e8_14)) (by simpa only [h7] using (Ne.symm e7_14))
      exact e13_14 (h13.trans h14.symm)
    ·
      have h7 : c 7 = 2 := force2 (c 7) b7 (by simpa only [h4] using (Ne.symm e4_7)) (by simpa only [h5] using (Ne.symm e5_7))
      have h9 : c 9 = 1 := force1 (c 9) b9 (by simpa only [h2] using (Ne.symm e2_9)) (by simpa only [h7] using (Ne.symm e7_9))
      have h10 : c 10 = 0 := force0 (c 10) b10 (by simpa only [h1] using (Ne.symm e1_10)) (by simpa only [h7] using (Ne.symm e7_10))
      have h11 : c 11 = 0 := force0 (c 11) b11 (by simpa only [h1] using (Ne.symm e1_11)) (by simpa only [h7] using (Ne.symm e7_11))
      have h6 : c 6 = 2 := force2 (c 6) b6 (by simpa only [h11] using e6_11) (by simpa only [h9] using e6_9)
      have h13 : c 13 = 2 := force2 (c 13) b13 (by simpa only [h2] using (Ne.symm e2_13)) (by simpa only [h3] using (Ne.symm e3_13))
      exact e6_13 (h6.trans h13.symm)

#print axioms not_three_colorable

end ToftDegreeFive

namespace ToftDegreeFive

theorem edge_deletion_colorable (e : Nat × Nat) (he : e ∈ edges) :
    ∃ c : Nat → Nat,
      (∀ v, v < 15 → c v < 3) ∧
      (∀ r ∈ edges, r ≠ e → c r.1 ≠ c r.2) := by
  have hm : e ∈ edgeWitnesses.map Prod.fst := by
    rw [edgeWitnesses_cover]
    exact he
  obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hm
  refine ⟨fun v => w.2.getD v 0, ?_, ?_⟩
  · intro v hv
    exact (edgeWitnesses_valid w hw).1 v (List.mem_range.mpr hv)
  · intro r hr hre
    apply (edgeWitnesses_valid w hw).2 r hr
    intro h
    exact hre (h.trans hwe)

theorem no_isolated_vertices :
    ∀ v ∈ List.range 15,
      ∃ e ∈ edges, e.1 = v ∨ e.2 = v := by
  decide

def ThreeColorable (V : List Nat) (E : List (Nat × Nat)) : Prop :=
  ∃ c : Nat → Nat,
    (∀ v ∈ V, c v < 3) ∧
    (∀ e ∈ E, c e.1 ≠ c e.2)

theorem every_proper_subgraph_three_colorable
    (V : List Nat) (E : List (Nat × Nat))
    (hv : ∀ v ∈ V, v < 15)
    (he : ∀ e ∈ E, e ∈ edges ∧ e.1 ∈ V ∧ e.2 ∈ V)
    (hproper :
      (∃ v, v < 15 ∧ v ∉ V) ∨
      (∃ e, e ∈ edges ∧ e ∉ E)) :
    ThreeColorable V E := by
  have missing_edge : ∃ e, e ∈ edges ∧ e ∉ E := by
    rcases hproper with ⟨v, hbound, hmissing⟩ | hmissing
    · obtain ⟨e, hedge, hincident⟩ :=
        no_isolated_vertices v (List.mem_range.mpr hbound)
      refine ⟨e, hedge, ?_⟩
      intro hin
      rcases hincident with h | h
      · have hend := (he e hin).2.1
        exact hmissing (h ▸ hend)
      · have hend := (he e hin).2.2
        exact hmissing (h ▸ hend)
    · exact hmissing
  obtain ⟨e, hedge, hmissing⟩ := missing_edge
  obtain ⟨c, hbound, hcolor⟩ := edge_deletion_colorable e hedge
  refine ⟨c, ?_, ?_⟩
  · intro v hin
    exact hbound v (hv v hin)
  · intro r hin
    apply hcolor r (he r hin).1
    intro h
    exact hmissing (h ▸ hin)

theorem not_threeColorable :
    ¬ ThreeColorable (List.range 15) edges := by
  rintro ⟨c, hbound, hcolor⟩
  apply not_three_colorable c
  · intro v hv
    exact hbound v (List.mem_range.mpr hv)
  · exact hcolor

#print axioms every_proper_subgraph_three_colorable
#print axioms not_threeColorable

end ToftDegreeFive

namespace ToftDegreeFive

def FourCritical : Prop :=
  (∃ c : Nat → Nat,
    (∀ v, v < 15 → c v < 4) ∧ Proper c) ∧
  (¬ ThreeColorable (List.range 15) edges) ∧
  (∀ (V : List Nat) (E : List (Nat × Nat)),
    (∀ v ∈ V, v < 15) →
    (∀ e ∈ E, e ∈ edges ∧ e.1 ∈ V ∧ e.2 ∈ V) →
    ((∃ v, v < 15 ∧ v ∉ V) ∨
     (∃ e, e ∈ edges ∧ e ∉ E)) →
    ThreeColorable V E)

theorem four_critical : FourCritical := by
  refine ⟨⟨fourColor, ?_, fourColor_proper⟩,
    not_threeColorable, ?_⟩
  · intro v hv
    exact fourColor_bound v (List.mem_range.mpr hv)
  · intro V E hv he hproper
    exact every_proper_subgraph_three_colorable V E hv he hproper

def forbidden (v : Nat) : Nat :=
  if v = 1 ∨ v = 2 then 0
  else if v = 3 ∨ v = 4 then 1
  else 2

theorem degree_five :
    ∃ N : List Nat,
      N.Nodup ∧ N.length = 5 ∧
      ∀ v, Adj 0 v ↔ v ∈ N := by
  exact ⟨[1,2,3,4,5], by decide, by decide, zero_neighbors⟩

theorem forbidden_bound :
    ∀ v ∈ ([1,2,3,4,5] : List Nat), forbidden v < 3 := by
  decide

theorem forbidden_nonconstant :
    ∃ u v, Adj 0 u ∧ Adj 0 v ∧ forbidden u ≠ forbidden v := by
  exact ⟨1, 3, by decide, by decide, by decide⟩

def AvoidingColoring (c : Nat → Nat) : Prop :=
  (∀ v, v < 15 → v ≠ 0 → c v < 3) ∧
  ProperWithoutZero c ∧
  (∀ v, Adj 0 v → c v ≠ forbidden v)

theorem no_avoidingColoring : ¬ ∃ c, AvoidingColoring c := by
  rintro ⟨c, hbound, hproper, havoid⟩
  exact no_avoiding_coloring c hbound hproper
    (by simpa [forbidden] using havoid 1 (by decide))
    (by simpa [forbidden] using havoid 2 (by decide))
    (by simpa [forbidden] using havoid 3 (by decide))
    (by simpa [forbidden] using havoid 4 (by decide))
    (by simpa [forbidden] using havoid 5 (by decide))

theorem counterexample :
    FourCritical ∧
    (∃ N : List Nat, N.Nodup ∧ N.length = 5 ∧
      ∀ v, Adj 0 v ↔ v ∈ N) ∧
    (∀ v ∈ ([1,2,3,4,5] : List Nat), forbidden v < 3) ∧
    (∃ u v, Adj 0 u ∧ Adj 0 v ∧ forbidden u ≠ forbidden v) ∧
    (¬ ∃ c, AvoidingColoring c) :=
  ⟨four_critical, degree_five, forbidden_bound,
   forbidden_nonconstant, no_avoidingColoring⟩

#print axioms counterexample

end ToftDegreeFive
