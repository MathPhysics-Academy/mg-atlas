import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Count
import Lean.Util.CollectAxioms

/- Shared definitions for finite graph/Farey certificates.
   No geometric fundamental-domain theorem is asserted. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace ChenFarey

structure Mat where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

noncomputable def det (m : Mat) : Int := m.a * m.d - m.b * m.c

noncomputable def neg (m : Mat) : Mat := ⟨-m.a,-m.b,-m.c,-m.d⟩

inductive Step where
  | s
  | t : Int → Step
  deriving DecidableEq

noncomputable def matrixStep (m : Mat) : Step → Mat
  | .s => ⟨m.b,-m.a,m.d,-m.c⟩
  | .t k => ⟨m.a,m.a*k+m.b,m.c,m.c*k+m.d⟩

noncomputable def matrixWord (w : List Step) : Mat := w.foldl matrixStep ⟨1,0,0,1⟩

noncomputable def pointStep {n : Nat} (S T Ti : Fin n → Fin n) (p : Fin n) : Step → Fin n
  | .s => S p
  | .t k => if k < 0 then (Ti^[k.natAbs]) p else (T^[k.natAbs]) p

noncomputable def pointWord {n : Nat} (S T Ti : Fin n → Fin n) (w : List Step) (p : Fin n) : Fin n :=
  w.foldl (pointStep S T Ti) p

structure Witness (n : Nat) where
  matrix : Mat
  word : List Step
  point : Fin n

noncomputable def WitnessValid {n : Nat} (S T Ti : Fin n → Fin n) (base : Fin n) (w : Witness n) : Prop :=
  det w.matrix = 1 ∧ (matrixWord w.word = w.matrix ∨ matrixWord w.word = neg w.matrix) ∧
    pointWord S T Ti w.word base = w.point

noncomputable instance {n : Nat} (S T Ti : Fin n → Fin n) (base : Fin n) (w : Witness n) :
    Decidable (WitnessValid S T Ti base w) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

noncomputable def follows {n : Nat} (P : Fin n → Fin n) (cs : List (Fin n)) : Bool :=
  !cs.isEmpty && (cs.zip (cs.drop 1 ++ cs.take 1)).all (fun pq => P pq.1 == pq.2)

noncomputable def adjacent (xs : List (Int × Int)) : List ((Int × Int) × (Int × Int)) :=
  xs.zip (xs.drop 1)

noncomputable def FareyNeighbor (pq : (Int × Int) × (Int × Int)) : Prop :=
  Int.natAbs (pq.1.1 * pq.2.2 - pq.2.1 * pq.1.2) = 1

noncomputable instance (pq : (Int × Int) × (Int × Int)) : Decidable (FareyNeighbor pq) :=
  inferInstanceAs (Decidable (_ = _))

theorem all_of_check {α : Type} (xs : List α) (P : α → Prop) [DecidablePred P]
    (h : xs.all (fun x => decide (P x)) = true) : ∀ x ∈ xs, P x := by
  simpa only [List.all_eq_true, decide_eq_true_eq] using h


noncomputable def mul (m n : Mat) : Mat :=
  ⟨m.a*n.a+m.b*n.c,m.a*n.b+m.b*n.d,m.c*n.a+m.d*n.c,m.c*n.b+m.d*n.d⟩
noncomputable def inv (m : Mat) : Mat := ⟨m.d,-m.b,-m.c,m.a⟩
noncomputable def samePSL (m n : Mat) : Prop := m = n ∨ m = neg n
noncomputable instance (m n : Mat) : Decidable (samePSL m n) := inferInstanceAs (Decidable (_ ∨ _))

noncomputable def sameCusp (p q : Int × Int) : Bool :=
  (p.1 != 0 || p.2 != 0) && (q.1 != 0 || q.2 != 0) && p.1*q.2 == q.1*p.2

noncomputable def matchesEdge (pq : (Int × Int) × (Int × Int)) (m : Mat) : Bool :=
  let a := (m.a,m.c)
  let b := (m.b,m.d)
  (sameCusp pq.1 a && sameCusp pq.2 b) || (sameCusp pq.1 b && sameCusp pq.2 a)

structure Side (n : Nat) where
  dart : Fin n
  label : Int -- -2 = even, -3 = odd, positive = free-pair label
  witness : Witness n

noncomputable def SideValid {n : Nat} (S T Ti : Fin n → Fin n) (base : Fin n)
    (lifts : Fin n → Mat) (side : Side n) : Prop :=
  WitnessValid S T Ti base side.witness ∧ side.witness.point = base ∧
  if side.label = -2 then
    S side.dart = side.dart ∧ samePSL side.witness.matrix
      (mul (mul (lifts side.dart) ⟨0,-1,1,0⟩) (inv (lifts side.dart)))
  else if side.label = -3 then
    T (S side.dart) = side.dart ∧ samePSL side.witness.matrix
      (mul (mul (lifts side.dart) ⟨0,-1,1,1⟩) (inv (lifts side.dart)))
  else
    0 < side.label ∧ S side.dart ≠ side.dart ∧ samePSL side.witness.matrix
      (mul (mul (lifts (S side.dart)) ⟨0,-1,1,0⟩) (inv (lifts side.dart)))

noncomputable instance {n : Nat} (S T Ti : Fin n → Fin n) (base : Fin n)
    (lifts : Fin n → Mat) (side : Side n) : Decidable (SideValid S T Ti base lifts side) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))



inductive LookupTree (α : Type) where
  | leaf : α → LookupTree α
  | branch : Nat → LookupTree α → LookupTree α → LookupTree α

noncomputable def tableLookup {α : Type} (tree : LookupTree α) (p : Nat) : α :=
  match tree with
  | .leaf value => value
  | .branch cut left right =>
      if p < cut then tableLookup left p else tableLookup right p

#print axioms tableLookup


theorem partition_from_index {n : Nat} (cs : List (List (Fin n)))
    (idx back : Fin n → Fin n) (left : ∀ p, back (idx p) = p)
    (h : cs.flatten.map idx = List.finRange n) :
    ∀ p : Fin n, (cs.flatten.filter (· == p)).length = 1 := by
  intro p
  have hinj : Function.Injective idx := fun a b hab =>
    (left a).symm.trans ((congrArg back hab).trans (left b))
  have hc := congrArg (List.count (idx p)) h
  rw [List.count_map_of_injective cs.flatten idx hinj p, List.count_finRange] at hc
  rw [← List.count_eq_length_filter]
  exact hc

#print axioms partition_from_index
namespace G240_93_c1
noncomputable def originalSData : LookupTree (Fin 120) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (8))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (12)) (.leaf (11))) (.branch 10 (.leaf (13)) (.leaf (15)))) (.branch 13 (.branch 12 (.leaf (17)) (.leaf (2))) (.branch 14 (.leaf (18)) (.leaf (21)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (19)) (.branch 17 (.leaf (23)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (25)) (.leaf (27))) (.branch 21 (.leaf (24)) (.leaf (26))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (31)) (.leaf (28))) (.branch 25 (.leaf (34)) (.leaf (9)))) (.branch 28 (.branch 27 (.leaf (35)) (.leaf (10))) (.branch 29 (.leaf (37)) (.leaf (39))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (41)) (.branch 32 (.leaf (36)) (.leaf (42)))) (.branch 35 (.branch 34 (.leaf (44)) (.leaf (38))) (.branch 36 (.leaf (14)) (.leaf (48))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (16)) (.leaf (20))) (.branch 40 (.leaf (46)) (.leaf (51)))) (.branch 43 (.branch 42 (.leaf (47)) (.leaf (49))) (.branch 44 (.leaf (54)) (.leaf (50)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (56)) (.branch 47 (.leaf (58)) (.leaf (60)))) (.branch 50 (.branch 49 (.leaf (22)) (.leaf (61))) (.branch 51 (.leaf (63)) (.leaf (59))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (66)) (.leaf (68))) (.branch 55 (.leaf (62)) (.leaf (71)))) (.branch 58 (.branch 57 (.leaf (64)) (.leaf (72))) (.branch 59 (.leaf (29)) (.leaf (75)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (30)) (.branch 62 (.leaf (32)) (.leaf (78)))) (.branch 65 (.branch 64 (.leaf (33)) (.leaf (80))) (.branch 66 (.leaf (82)) (.leaf (76))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (65)) (.leaf (77))) (.branch 70 (.leaf (74)) (.leaf (85)))) (.branch 73 (.branch 72 (.leaf (79)) (.leaf (81))) (.branch 74 (.leaf (87)) (.leaf (88)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (40)) (.branch 77 (.leaf (91)) (.leaf (92)))) (.branch 80 (.branch 79 (.leaf (43)) (.leaf (94))) (.branch 81 (.leaf (45)) (.leaf (95))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (90)) (.leaf (84))) (.branch 85 (.leaf (98)) (.leaf (93)))) (.branch 88 (.branch 87 (.leaf (70)) (.leaf (96))) (.branch 89 (.leaf (97)) (.leaf (99))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (67)) (.branch 92 (.leaf (52)) (.leaf (53)))) (.branch 95 (.branch 94 (.leaf (86)) (.leaf (55))) (.branch 96 (.leaf (57)) (.leaf (102))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (69)) (.leaf (101))) (.branch 100 (.leaf (103)) (.leaf (104)))) (.branch 103 (.branch 102 (.leaf (83)) (.leaf (73))) (.branch 104 (.leaf (106)) (.leaf (107)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (109)) (.branch 107 (.leaf (89)) (.leaf (111)))) (.branch 110 (.branch 109 (.leaf (110)) (.leaf (112))) (.branch 111 (.leaf (115)) (.leaf (100))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (116)) (.leaf (118))) (.branch 115 (.leaf (113)) (.leaf (117)))) (.branch 118 (.branch 117 (.leaf (105)) (.leaf (108))) (.branch 119 (.leaf (119)) (.leaf (114)))))))))
noncomputable def originalS (p : Fin 120) : Fin 120 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 120) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (9))) (.branch 6 (.leaf (10)) (.leaf (11))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (5))) (.branch 10 (.leaf (14)) (.leaf (16)))) (.branch 13 (.branch 12 (.leaf (18)) (.leaf (19))) (.branch 14 (.leaf (20)) (.leaf (22)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (1)) (.branch 17 (.leaf (24)) (.leaf (12)))) (.branch 20 (.branch 19 (.leaf (26)) (.leaf (28))) (.branch 21 (.leaf (29)) (.leaf (30))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (32)) (.leaf (33))) (.branch 25 (.leaf (8)) (.leaf (34)))) (.branch 28 (.branch 27 (.leaf (36)) (.leaf (6))) (.branch 29 (.leaf (38)) (.leaf (40))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (35)) (.branch 32 (.leaf (41)) (.leaf (43)))) (.branch 35 (.branch 34 (.leaf (45)) (.leaf (46))) (.branch 36 (.leaf (47)) (.leaf (49))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (50)) (.leaf (17))) (.branch 40 (.leaf (37)) (.leaf (52)))) (.branch 43 (.branch 42 (.leaf (13)) (.leaf (53))) (.branch 44 (.leaf (55)) (.leaf (15)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (57)) (.branch 47 (.leaf (59)) (.leaf (21)))) (.branch 50 (.branch 49 (.leaf (60)) (.leaf (62))) (.branch 51 (.leaf (64)) (.leaf (65))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (67)) (.leaf (69))) (.branch 55 (.leaf (70)) (.leaf (72)))) (.branch 58 (.branch 57 (.leaf (73)) (.leaf (74))) (.branch 59 (.leaf (23)) (.leaf (76)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (25)) (.branch 62 (.leaf (77)) (.leaf (79)))) (.branch 65 (.branch 64 (.leaf (27)) (.leaf (81))) (.branch 66 (.leaf (83)) (.leaf (84))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (58)) (.leaf (31))) (.branch 70 (.leaf (71)) (.leaf (54)))) (.branch 73 (.branch 72 (.leaf (86)) (.leaf (87))) (.branch 74 (.leaf (80)) (.leaf (89)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (90)) (.branch 77 (.leaf (82)) (.leaf (88)))) (.branch 80 (.branch 79 (.leaf (93)) (.leaf (95))) (.branch 81 (.leaf (96)) (.leaf (97))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (39)) (.leaf (75))) (.branch 85 (.leaf (66)) (.leaf (42)))) (.branch 88 (.branch 87 (.leaf (61)) (.leaf (44))) (.branch 89 (.leaf (94)) (.leaf (100))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (98)) (.branch 92 (.leaf (101)) (.leaf (48)))) (.branch 95 (.branch 94 (.leaf (78)) (.leaf (85))) (.branch 96 (.leaf (102)) (.leaf (56))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (103)) (.leaf (51))) (.branch 100 (.leaf (68)) (.leaf (105)))) (.branch 103 (.branch 102 (.leaf (91)) (.leaf (63))) (.branch 104 (.leaf (107)) (.leaf (108)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (110)) (.branch 107 (.leaf (92)) (.leaf (112)))) (.branch 110 (.branch 109 (.leaf (113)) (.leaf (114))) (.branch 111 (.leaf (99)) (.leaf (115))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (117)) (.leaf (104))) (.branch 115 (.leaf (109)) (.leaf (119)))) (.branch 118 (.branch 117 (.leaf (118)) (.leaf (106))) (.branch 119 (.leaf (116)) (.leaf (111)))))))))
noncomputable def originalT (p : Fin 120) : Fin 120 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 60) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (8)) (.leaf (9)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (10)) (.branch 17 (.leaf (11)) (.leaf (5)))) (.branch 20 (.branch 19 (.leaf (6)) (.leaf (7))) (.branch 21 (.leaf (12)) (.leaf (13))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (14)) (.leaf (15))) (.branch 25 (.leaf (16)) (.leaf (8)))) (.branch 28 (.branch 27 (.leaf (9)) (.leaf (10))) (.branch 29 (.leaf (11)) (.leaf (17))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (18)) (.branch 32 (.leaf (19)) (.leaf (20)))) (.branch 35 (.branch 34 (.leaf (21)) (.leaf (12))) (.branch 36 (.leaf (13)) (.leaf (14))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (15)) (.leaf (16))) (.branch 40 (.leaf (22)) (.leaf (23)))) (.branch 43 (.branch 42 (.leaf (24)) (.leaf (25))) (.branch 44 (.leaf (26)) (.leaf (27)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (28)) (.branch 47 (.leaf (17)) (.leaf (18)))) (.branch 50 (.branch 49 (.leaf (19)) (.leaf (20))) (.branch 51 (.leaf (21)) (.leaf (29))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (30)) (.leaf (31))) (.branch 55 (.leaf (32)) (.leaf (33)))) (.branch 58 (.branch 57 (.leaf (34)) (.leaf (35))) (.branch 59 (.leaf (22)) (.leaf (23)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (24)) (.branch 62 (.leaf (25)) (.leaf (26)))) (.branch 65 (.branch 64 (.leaf (27)) (.leaf (28))) (.branch 66 (.leaf (36)) (.leaf (37))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (38)) (.leaf (39))) (.branch 70 (.leaf (40)) (.leaf (41)))) (.branch 73 (.branch 72 (.leaf (42)) (.leaf (43))) (.branch 74 (.leaf (44)) (.leaf (45)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (29)) (.branch 77 (.leaf (30)) (.leaf (31)))) (.branch 80 (.branch 79 (.leaf (32)) (.leaf (33))) (.branch 81 (.leaf (34)) (.leaf (35))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (38)) (.leaf (46))) (.branch 85 (.leaf (47)) (.leaf (48)))) (.branch 88 (.branch 87 (.leaf (48)) (.leaf (49))) (.branch 89 (.leaf (40)) (.leaf (50))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (36)) (.branch 92 (.leaf (37)) (.leaf (39)))) (.branch 95 (.branch 94 (.leaf (41)) (.leaf (42))) (.branch 96 (.leaf (43)) (.leaf (44))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (45)) (.leaf (46))) (.branch 100 (.leaf (51)) (.leaf (52)))) (.branch 103 (.branch 102 (.leaf (47)) (.leaf (49))) (.branch 104 (.leaf (50)) (.leaf (53)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (54)) (.branch 107 (.leaf (51)) (.leaf (52)))) (.branch 110 (.branch 109 (.leaf (55)) (.leaf (56))) (.branch 111 (.leaf (57)) (.leaf (53))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (54)) (.leaf (58))) (.branch 115 (.leaf (59)) (.leaf (55)))) (.branch 118 (.branch 117 (.leaf (56)) (.leaf (57))) (.branch 119 (.leaf (59)) (.leaf (58)))))))))
noncomputable def projection (p : Fin 120) : Fin 60 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 120) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (5))) (.branch 6 (.leaf (8)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (10)) (.leaf (13))) (.branch 10 (.leaf (14)) (.leaf (15)))) (.branch 13 (.branch 12 (.leaf (16)) (.leaf (20))) (.branch 14 (.leaf (21)) (.leaf (22)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (23)) (.branch 17 (.leaf (24)) (.leaf (29)))) (.branch 20 (.branch 19 (.leaf (30)) (.leaf (31))) (.branch 21 (.leaf (32)) (.leaf (33))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (39)) (.leaf (40))) (.branch 25 (.leaf (41)) (.leaf (42)))) (.branch 28 (.branch 27 (.leaf (43)) (.leaf (44))) (.branch 29 (.leaf (45)) (.leaf (51))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (52)) (.branch 32 (.leaf (53)) (.leaf (54)))) (.branch 35 (.branch 34 (.leaf (55)) (.leaf (56))) (.branch 36 (.leaf (57)) (.leaf (65))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (66)) (.leaf (67))) (.branch 40 (.leaf (68)) (.leaf (69)))) (.branch 43 (.branch 42 (.leaf (70)) (.leaf (71))) (.branch 44 (.leaf (72)) (.leaf (73)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (74)) (.branch 47 (.leaf (83)) (.leaf (84)))) (.branch 50 (.branch 49 (.leaf (85)) (.leaf (87))) (.branch 51 (.leaf (89)) (.leaf (99))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (100)) (.leaf (104))) (.branch 55 (.leaf (105)) (.leaf (108)))) (.branch 58 (.branch 57 (.leaf (109)) (.leaf (110))) (.branch 59 (.leaf (113)) (.leaf (114))))))))
noncomputable def representative (p : Fin 60) : Fin 120 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (3)) (.leaf (8))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (10)) (.leaf (6))) (.branch 10 (.leaf (13)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (15)) (.leaf (16))) (.branch 14 (.leaf (9)) (.leaf (19)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (11)) (.branch 17 (.leaf (12)) (.leaf (22)))) (.branch 20 (.branch 19 (.leaf (24)) (.leaf (14))) (.branch 21 (.leaf (25)) (.leaf (27))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (17)) (.leaf (29))) (.branch 25 (.leaf (18)) (.leaf (20)))) (.branch 28 (.branch 27 (.leaf (32)) (.leaf (21))) (.branch 29 (.leaf (34)) (.leaf (23))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (37)) (.branch 32 (.leaf (39)) (.leaf (26)))) (.branch 35 (.branch 34 (.leaf (42)) (.leaf (28))) (.branch 36 (.leaf (43)) (.leaf (38))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (30)) (.leaf (36))) (.branch 40 (.leaf (31)) (.leaf (45)))) (.branch 43 (.branch 42 (.leaf (48)) (.leaf (33))) (.branch 44 (.leaf (35)) (.leaf (49)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (40)) (.branch 47 (.leaf (47)) (.leaf (46)))) (.branch 50 (.branch 49 (.leaf (41)) (.leaf (44))) (.branch 51 (.leaf (51)) (.leaf (50))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (53)) (.leaf (52))) (.branch 55 (.leaf (56)) (.leaf (57)))) (.branch 58 (.branch 57 (.leaf (54)) (.leaf (55))) (.branch 59 (.leaf (59)) (.leaf (58))))))))
noncomputable def S (p : Fin 60) : Fin 60 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (7))) (.branch 6 (.leaf (4)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (11)) (.leaf (12))) (.branch 10 (.leaf (14)) (.leaf (1)))) (.branch 13 (.branch 12 (.leaf (16)) (.leaf (17))) (.branch 14 (.leaf (18)) (.leaf (20)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (21)) (.branch 17 (.leaf (5)) (.leaf (23)))) (.branch 20 (.branch 19 (.leaf (13)) (.leaf (24))) (.branch 21 (.leaf (26)) (.leaf (28))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (15)) (.leaf (30))) (.branch 25 (.leaf (8)) (.leaf (31)))) (.branch 28 (.branch 27 (.leaf (33)) (.leaf (10))) (.branch 29 (.leaf (35)) (.leaf (36))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (38)) (.branch 32 (.leaf (40)) (.leaf (41)))) (.branch 35 (.branch 34 (.leaf (43)) (.leaf (44))) (.branch 36 (.leaf (45)) (.leaf (46))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (47)) (.leaf (22))) (.branch 40 (.leaf (19)) (.leaf (42)))) (.branch 43 (.branch 42 (.leaf (32)) (.leaf (48))) (.branch 44 (.leaf (49)) (.leaf (34)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (50)) (.branch 47 (.leaf (29)) (.leaf (37)))) (.branch 50 (.branch 49 (.leaf (25)) (.leaf (27))) (.branch 51 (.leaf (52)) (.leaf (39))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (54)) (.leaf (55))) (.branch 55 (.leaf (57)) (.leaf (58)))) (.branch 58 (.branch 57 (.leaf (59)) (.leaf (51))) (.branch 59 (.leaf (53)) (.leaf (56))))))))
noncomputable def T (p : Fin 60) : Fin 60 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (10)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (5))) (.branch 6 (.leaf (16)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (24))) (.branch 10 (.leaf (6)) (.leaf (27)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 14 (.leaf (18)) (.leaf (9)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (22)) (.branch 17 (.leaf (11)) (.leaf (12)))) (.branch 20 (.branch 19 (.leaf (13)) (.leaf (39))) (.branch 21 (.leaf (14)) (.leaf (15))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (38)) (.leaf (17))) (.branch 25 (.leaf (19)) (.leaf (48)))) (.branch 28 (.branch 27 (.leaf (20)) (.leaf (49))) (.branch 29 (.leaf (21)) (.leaf (46))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (23)) (.branch 32 (.leaf (25)) (.leaf (41)))) (.branch 35 (.branch 34 (.leaf (26)) (.leaf (44))) (.branch 36 (.leaf (28)) (.leaf (29))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (47)) (.leaf (30))) (.branch 40 (.leaf (51)) (.leaf (31)))) (.branch 43 (.branch 42 (.leaf (32)) (.leaf (40))) (.branch 44 (.leaf (33)) (.leaf (34)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (35)) (.branch 47 (.leaf (36)) (.leaf (37)))) (.branch 50 (.branch 49 (.leaf (42)) (.leaf (43))) (.branch 51 (.leaf (45)) (.leaf (57))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (50)) (.leaf (58))) (.branch 55 (.leaf (52)) (.leaf (53)))) (.branch 58 (.branch 57 (.leaf (59)) (.leaf (54))) (.branch 59 (.leaf (55)) (.leaf (56))))))))
noncomputable def Ti (p : Fin 60) : Fin 60 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 60) : Fin 60 := T (S p)
theorem quotient_relations : (∀ p : Fin 60, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 120, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 120, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 60, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 60)) := [[0,3,4],[1,2,7],[5,6,12],[8,9,18],[10,11,21],[13,14,24],[15,16,17],[19,20,31],[22,23,36],[25,26,41],[27,28,44],[29,30,47],[32,33,48],[34,35,49],[37,38,46],[39,40,50],[42,43,45],[51,52,55],[53,54,59],[56,57,58]]
noncomputable def verticesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (6)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (9))) (.branch 10 (.leaf (10)) (.leaf (12)))) (.branch 13 (.branch 12 (.leaf (13)) (.leaf (8))) (.branch 14 (.leaf (15)) (.leaf (16)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (18)) (.branch 17 (.leaf (19)) (.leaf (20)))) (.branch 20 (.branch 19 (.leaf (11)) (.leaf (21))) (.branch 21 (.leaf (22)) (.leaf (14))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (24)) (.leaf (25))) (.branch 25 (.leaf (17)) (.leaf (27)))) (.branch 28 (.branch 27 (.leaf (28)) (.leaf (30))) (.branch 29 (.leaf (31)) (.leaf (33))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (34)) (.branch 32 (.leaf (23)) (.leaf (36)))) (.branch 35 (.branch 34 (.leaf (37)) (.leaf (39))) (.branch 36 (.leaf (40)) (.leaf (26))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (42)) (.leaf (43))) (.branch 40 (.leaf (45)) (.leaf (46)))) (.branch 43 (.branch 42 (.leaf (29)) (.leaf (48))) (.branch 44 (.leaf (49)) (.leaf (32)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (50)) (.branch 47 (.leaf (44)) (.leaf (35)))) (.branch 50 (.branch 49 (.leaf (38)) (.leaf (41))) (.branch 51 (.leaf (47)) (.leaf (51))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (52)) (.leaf (54))) (.branch 55 (.leaf (55)) (.leaf (53)))) (.branch 58 (.branch 57 (.leaf (57)) (.leaf (58))) (.branch 59 (.leaf (59)) (.leaf (56))))))))
noncomputable def verticesIndex (p : Fin 60) : Fin 60 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (7)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (12))) (.branch 10 (.leaf (8)) (.leaf (9)))) (.branch 13 (.branch 12 (.leaf (18)) (.leaf (10))) (.branch 14 (.leaf (11)) (.leaf (21)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (13)) (.branch 17 (.leaf (14)) (.leaf (24)))) (.branch 20 (.branch 19 (.leaf (15)) (.leaf (16))) (.branch 21 (.leaf (17)) (.leaf (19))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (20)) (.leaf (31))) (.branch 25 (.leaf (22)) (.leaf (23)))) (.branch 28 (.branch 27 (.leaf (36)) (.leaf (25))) (.branch 29 (.leaf (26)) (.leaf (41))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (28)) (.leaf (44)))) (.branch 35 (.branch 34 (.leaf (29)) (.leaf (30))) (.branch 36 (.leaf (47)) (.leaf (32))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (33)) (.leaf (48))) (.branch 40 (.leaf (34)) (.leaf (35)))) (.branch 43 (.branch 42 (.leaf (49)) (.leaf (37))) (.branch 44 (.leaf (38)) (.leaf (46)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (39)) (.branch 47 (.leaf (40)) (.leaf (50)))) (.branch 50 (.branch 49 (.leaf (42)) (.leaf (43))) (.branch 51 (.leaf (45)) (.leaf (51))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (52)) (.leaf (55))) (.branch 55 (.leaf (53)) (.leaf (54)))) (.branch 58 (.branch 57 (.leaf (59)) (.leaf (56))) (.branch 59 (.leaf (57)) (.leaf (58))))))))
noncomputable def verticesBack (p : Fin 60) : Fin 60 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 60, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 60 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 60, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 60)) := [[0,1],[2,4],[3,5],[6,8],[7,10],[9,13],[11,15],[12,16],[14,19],[17,22],[18,24],[20,25],[21,27],[23,29],[26,32],[28,34],[30,37],[31,39],[33,42],[35,43],[36,38],[40,45],[41,48],[44,49],[46,47],[50,51],[52,53],[54,56],[55,57],[58,59]]
noncomputable def edgesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (7))) (.branch 10 (.leaf (10)) (.leaf (9)))) (.branch 13 (.branch 12 (.leaf (12)) (.leaf (14))) (.branch 14 (.leaf (11)) (.leaf (16)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (13)) (.branch 17 (.leaf (15)) (.leaf (18)))) (.branch 20 (.branch 19 (.leaf (20)) (.leaf (17))) (.branch 21 (.leaf (22)) (.leaf (24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (19)) (.leaf (26))) (.branch 25 (.leaf (21)) (.leaf (23)))) (.branch 28 (.branch 27 (.leaf (28)) (.leaf (25))) (.branch 29 (.leaf (30)) (.leaf (27))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (32)) (.branch 32 (.leaf (34)) (.leaf (29)))) (.branch 35 (.branch 34 (.leaf (36)) (.leaf (31))) (.branch 36 (.leaf (38)) (.leaf (40))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (33)) (.leaf (41))) (.branch 40 (.leaf (35)) (.leaf (42)))) (.branch 43 (.branch 42 (.leaf (44)) (.leaf (37))) (.branch 44 (.leaf (39)) (.leaf (46)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (43)) (.branch 47 (.leaf (48)) (.leaf (49)))) (.branch 50 (.branch 49 (.leaf (45)) (.leaf (47))) (.branch 51 (.leaf (50)) (.leaf (51))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (52)) (.leaf (53))) (.branch 55 (.leaf (54)) (.leaf (56)))) (.branch 58 (.branch 57 (.leaf (55)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (59))))))))
noncomputable def edgesIndex (p : Fin 60) : Fin 60 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (7))) (.branch 10 (.leaf (10)) (.leaf (9)))) (.branch 13 (.branch 12 (.leaf (13)) (.leaf (11))) (.branch 14 (.leaf (15)) (.leaf (12)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (16)) (.branch 17 (.leaf (14)) (.leaf (19)))) (.branch 20 (.branch 19 (.leaf (17)) (.leaf (22))) (.branch 21 (.leaf (18)) (.leaf (24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (20)) (.leaf (25))) (.branch 25 (.leaf (21)) (.leaf (27)))) (.branch 28 (.branch 27 (.leaf (23)) (.leaf (29))) (.branch 29 (.leaf (26)) (.leaf (32))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (28)) (.branch 32 (.leaf (34)) (.leaf (30)))) (.branch 35 (.branch 34 (.leaf (37)) (.leaf (31))) (.branch 36 (.leaf (39)) (.leaf (33))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (42)) (.leaf (35))) (.branch 40 (.leaf (43)) (.leaf (36)))) (.branch 43 (.branch 42 (.leaf (38)) (.leaf (40))) (.branch 44 (.leaf (45)) (.leaf (41)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (48)) (.branch 47 (.leaf (44)) (.leaf (49)))) (.branch 50 (.branch 49 (.leaf (46)) (.leaf (47))) (.branch 51 (.leaf (50)) (.leaf (51))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (52)) (.leaf (53))) (.branch 55 (.leaf (54)) (.leaf (56)))) (.branch 58 (.branch 57 (.leaf (55)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (59))))))))
noncomputable def edgesBack (p : Fin 60) : Fin 60 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 60, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 60 := by decide +kernel
theorem edges_partition : ∀ p : Fin 60, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 60)) := [[0,2],[1,3,6,9,14,20,26,33,43,49,27,10],[4,7,11,16,5],[8,12,17,23,30,38,22,15,21,28,35,45,50,52,54,57,51,39,19,24],[13,18],[25,31,40,42,48],[29,36,46],[32,41],[34,44],[37,47],[53,55,58],[56,59]]
noncomputable def facesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (14))) (.branch 6 (.leaf (18)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (15)) (.leaf (19))) (.branch 10 (.leaf (5)) (.leaf (13)))) (.branch 13 (.branch 12 (.leaf (16)) (.leaf (20))) (.branch 14 (.leaf (39)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (26)) (.branch 17 (.leaf (17)) (.leaf (21)))) (.branch 20 (.branch 19 (.leaf (40)) (.leaf (37))) (.branch 21 (.leaf (7)) (.leaf (27))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (25)) (.leaf (22))) (.branch 25 (.leaf (38)) (.leaf (41)))) (.branch 28 (.branch 27 (.leaf (8)) (.leaf (12))) (.branch 29 (.leaf (28)) (.leaf (46))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (23)) (.branch 32 (.leaf (42)) (.leaf (49)))) (.branch 35 (.branch 34 (.leaf (9)) (.leaf (51))) (.branch 36 (.leaf (29)) (.leaf (47))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (53)) (.leaf (24))) (.branch 40 (.leaf (36)) (.leaf (43)))) (.branch 43 (.branch 42 (.leaf (50)) (.leaf (44))) (.branch 44 (.leaf (10)) (.leaf (52)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (30)) (.branch 47 (.leaf (48)) (.leaf (54)))) (.branch 50 (.branch 49 (.leaf (45)) (.leaf (11))) (.branch 51 (.leaf (31)) (.leaf (35))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (32)) (.leaf (55))) (.branch 55 (.leaf (33)) (.leaf (56)))) (.branch 58 (.branch 57 (.leaf (58)) (.leaf (34))) (.branch 59 (.leaf (57)) (.leaf (59))))))))
noncomputable def facesIndex (p : Fin 60) : Fin 60 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (6))) (.branch 6 (.leaf (9)) (.leaf (14))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (20)) (.leaf (26))) (.branch 10 (.leaf (33)) (.leaf (43)))) (.branch 13 (.branch 12 (.leaf (49)) (.leaf (27))) (.branch 14 (.leaf (10)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (7)) (.branch 17 (.leaf (11)) (.leaf (16)))) (.branch 20 (.branch 19 (.leaf (5)) (.leaf (8))) (.branch 21 (.leaf (12)) (.leaf (17))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (23)) (.leaf (30))) (.branch 25 (.leaf (38)) (.leaf (22)))) (.branch 28 (.branch 27 (.leaf (15)) (.leaf (21))) (.branch 29 (.leaf (28)) (.leaf (35))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (45)) (.branch 32 (.leaf (50)) (.leaf (52)))) (.branch 35 (.branch 34 (.leaf (54)) (.leaf (57))) (.branch 36 (.leaf (51)) (.leaf (39))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (19)) (.leaf (24))) (.branch 40 (.leaf (13)) (.leaf (18)))) (.branch 43 (.branch 42 (.leaf (25)) (.leaf (31))) (.branch 44 (.leaf (40)) (.leaf (42)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (48)) (.branch 47 (.leaf (29)) (.leaf (36)))) (.branch 50 (.branch 49 (.leaf (46)) (.leaf (32))) (.branch 51 (.leaf (41)) (.leaf (34))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (44)) (.leaf (37))) (.branch 55 (.leaf (47)) (.leaf (53)))) (.branch 58 (.branch 57 (.leaf (55)) (.leaf (58))) (.branch 59 (.leaf (56)) (.leaf (59))))))))
noncomputable def facesBack (p : Fin 60) : Fin 60 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 60, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 60 := by decide +kernel
theorem faces_partition : ∀ p : Fin 60, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [2,12,5,20,2,5,3,2,2,2,3,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 20 - 30 + 12 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 5 (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 6 (.leaf (⟨-1,0,1,-1⟩)) (.leaf (⟨0,1,-1,-2⟩))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨1,0,-2,1⟩))) (.branch 10 (.leaf (⟨0,-1,1,3⟩)) (.leaf (⟨0,1,-1,1⟩)))) (.branch 13 (.branch 12 (.leaf (⟨1,1,1,2⟩)) (.leaf (⟨1,1,-2,-1⟩))) (.branch 14 (.leaf (⟨-1,0,3,-1⟩)) (.leaf (⟨0,1,-1,-4⟩)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (⟨-2,-1,3,1⟩)) (.branch 17 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-2,2,3⟩)))) (.branch 20 (.branch 19 (.leaf (⟨-1,-1,3,2⟩)) (.leaf (⟨1,0,-4,1⟩))) (.branch 21 (.leaf (⟨0,-1,1,5⟩)) (.leaf (⟨1,0,2,1⟩))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (⟨-2,1,3,-2⟩)) (.leaf (⟨1,3,-2,-5⟩))) (.branch 25 (.leaf (⟨1,1,-4,-3⟩)) (.leaf (⟨-1,0,5,-1⟩)))) (.branch 28 (.branch 27 (.leaf (⟨0,1,-1,-6⟩)) (.leaf (⟨0,-1,1,-2⟩))) (.branch 29 (.leaf (⟨-1,-1,-2,-3⟩)) (.leaf (⟨3,-1,-5,2⟩))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (⟨-1,-4,2,7⟩)) (.branch 32 (.leaf (⟨-1,-1,5,4⟩)) (.leaf (⟨5,2,12,5⟩)))) (.branch 35 (.branch 34 (.leaf (⟨-2,3,-5,7⟩)) (.leaf (⟨-1,1,-3,2⟩))) (.branch 36 (.leaf (⟨1,2,2,5⟩)) (.leaf (⟨3,2,-5,-3⟩))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (⟨-5,-2,8,3⟩)) (.leaf (⟨2,-3,-3,5⟩))) (.branch 40 (.leaf (⟨-1,1,4,-5⟩)) (.leaf (⟨1,2,-5,-9⟩)))) (.branch 43 (.branch 42 (.leaf (⟨1,1,-6,-5⟩)) (.leaf (⟨-3,-2,-7,-5⟩))) (.branch 44 (.leaf (⟨2,-1,5,-2⟩)) (.leaf (⟨-1,0,-3,-1⟩)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (⟨-1,-3,-2,-7⟩)) (.branch 47 (.leaf (⟨-3,-5,5,8⟩)) (.leaf (⟨-4,-3,7,5⟩)))) (.branch 50 (.branch 49 (.leaf (⟨3,5,7,12⟩)) (.leaf (⟨2,1,5,3⟩))) (.branch 51 (.leaf (⟨2,1,-9,-4⟩)) (.leaf (⟨1,-2,-4,9⟩))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (⟨-2,-3,9,13⟩)) (.leaf (⟨-3,2,13,-9⟩))) (.branch 55 (.leaf (⟨2,5,-9,-22⟩)) (.leaf (⟨-3,-1,13,4⟩)))) (.branch 58 (.branch 57 (.leaf (⟨4,1,-17,-4⟩)) (.leaf (⟨-1,3,4,-13⟩))) (.branch 59 (.leaf (⟨3,4,-13,-17⟩)) (.leaf (⟨5,3,-22,-13⟩))))))))
noncomputable def liftMatrix (p : Fin 60) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 60) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],4⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],5⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],6⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],7⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],8⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],9⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],10⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],11⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨-1,0,3,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],13⟩,⟨⟨0,1,-1,-4⟩,[.t (0),.s,.t (4)],14⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],15⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],16⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],17⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],18⟩,⟨⟨1,0,-4,1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],19⟩,⟨⟨0,-1,1,5⟩,[.t (0),.s,.t (5)],20⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],21⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],22⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],23⟩,⟨⟨1,1,-4,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],24⟩,⟨⟨-1,0,5,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],25⟩,⟨⟨0,1,-1,-6⟩,[.t (0),.s,.t (6)],26⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],27⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],28⟩,⟨⟨3,-1,-5,2⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-1)],29⟩,⟨⟨-1,-4,2,7⟩,[.t (-1),.s,.t (-2),.s,.t (3)],30⟩,⟨⟨-1,-1,5,4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],31⟩,⟨⟨5,2,12,5⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (0)],32⟩,⟨⟨-2,3,-5,7⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2)],33⟩,⟨⟨-1,1,-3,2⟩,[.t (0),.s,.t (-3),.s,.t (-1)],34⟩,⟨⟨1,2,2,5⟩,[.t (0),.s,.t (-2),.s,.t (2)],35⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],36⟩,⟨⟨-5,-2,8,3⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (0)],37⟩,⟨⟨2,-3,-3,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2)],38⟩,⟨⟨-1,1,4,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],39⟩,⟨⟨1,2,-5,-9⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],40⟩,⟨⟨1,1,-6,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],41⟩,⟨⟨-3,-2,-7,-5⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],42⟩,⟨⟨2,-1,5,-2⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-1)],43⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],44⟩,⟨⟨-1,-3,-2,-7⟩,[.t (0),.s,.t (-2),.s,.t (3)],45⟩,⟨⟨-3,-5,5,8⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (1)],46⟩,⟨⟨-4,-3,7,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],47⟩,⟨⟨3,5,7,12⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (1)],48⟩,⟨⟨2,1,5,3⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (0)],49⟩,⟨⟨2,1,-9,-4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],50⟩,⟨⟨1,-2,-4,9⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3)],51⟩,⟨⟨-2,-3,9,13⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (1)],52⟩,⟨⟨-3,2,13,-9⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-1)],53⟩,⟨⟨2,5,-9,-22⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (2)],54⟩,⟨⟨-3,-1,13,4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (0)],55⟩,⟨⟨4,1,-17,-4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (0)],56⟩,⟨⟨-1,3,4,-13⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4)],57⟩,⟨⟨3,4,-13,-17⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (1)],58⟩,⟨⟨5,3,-22,-13⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (0)],59⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 60 ∧ ((List.finRange 60).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 60) := [⟨4,1,⟨⟨1,2,0,1⟩,[.t (2)],0⟩⟩,⟨15,2,⟨⟨-4,-3,-5,-4⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨37,5,⟨⟨20,13,-37,-24⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨46,9,⟨⟨-44,-27,75,46⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨47,9,⟨⟨46,27,-75,-44⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨30,5,⟨⟨-24,-13,37,20⟩,[.t (-1),.s,.t (-3),.s,.t (-7),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨18,3,⟨⟨5,2,-18,-7⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨24,3,⟨⟨-7,-2,18,5⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨56,10,⟨⟨54,13,-241,-58⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨58,11,⟨⟨-116,-27,507,118⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨59,11,⟨⟨118,27,-507,-116⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨54,10,⟨⟨-58,-13,241,54⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-8),.s,.t (-2),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨40,6,⟨⟨32,7,73,16⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨41,7,⟨⟨-43,-8,-102,-19⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-6),.s,.t (0)],0⟩⟩,⟨26,4,⟨⟨-17,-2,-42,-5⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-9),.s,.t (0)],0⟩⟩,⟨44,8,⟨⟨-7,2,-18,5⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨49,8,⟨⟨5,-2,18,-7⟩,[.t (0),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨32,4,⟨⟨-5,2,42,-17⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨48,7,⟨⟨-19,8,102,-43⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-4),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨45,6,⟨⟨16,-7,-73,32⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-5),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨11,2,⟨⟨-4,3,5,-4⟩,[.t (-1),.s,.t (-5),.s,.t (-1)],0⟩⟩,⟨2,1,⟨⟨1,-2,0,1⟩,[.t (-2)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-2,3),(-5,8),(-3,5),(-4,7),(-1,2),(-1,3),(-1,4),(-4,17),(-3,13),(-5,22),(-2,9),(-1,5),(-1,6),(0,1),(1,3),(2,5),(5,12),(3,7),(1,2),(1,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G240_93_c1

-- Audit all transitive dependencies, including generated auxiliary definitions.
run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.toString.startsWith "ChenFarey." then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Axiom audit failed: {name} depends on {ax}"
      count := count + 1
  Lean.logInfo m!"Axiom audit passed for all {count} ChenFarey declarations; allowed: {allowed}"

end ChenFarey
