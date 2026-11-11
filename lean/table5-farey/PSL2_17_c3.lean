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
namespace PSL2_17_c3
noncomputable def originalSData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (8))) (.branch 7 (.leaf (11)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (13))) (.branch 11 (.leaf (4)) (.leaf (15)))) (.branch 14 (.branch 13 (.leaf (19)) (.leaf (10))) (.branch 15 (.leaf (2)) (.leaf (21)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (18)) (.leaf (23))) (.branch 19 (.leaf (17)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (25)) (.leaf (6))) (.branch 23 (.leaf (27)) (.leaf (16))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (29)) (.leaf (28))) (.branch 27 (.leaf (24)) (.leaf (12)))) (.branch 30 (.branch 29 (.leaf (33)) (.leaf (32))) (.branch 31 (.leaf (34)) (.leaf (36))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (26)) (.leaf (20))) (.branch 35 (.leaf (38)) (.leaf (40)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (42))) (.branch 39 (.leaf (44)) (.leaf (46))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (45)) (.leaf (49))) (.branch 43 (.leaf (47)) (.leaf (52)))) (.branch 46 (.branch 45 (.leaf (30)) (.leaf (54))) (.branch 47 (.leaf (31)) (.leaf (56)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (58)) (.leaf (55))) (.branch 51 (.leaf (61)) (.leaf (62)))) (.branch 54 (.branch 53 (.leaf (57)) (.leaf (65))) (.branch 55 (.leaf (35)) (.leaf (68))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (37)) (.leaf (71))) (.branch 59 (.leaf (67)) (.leaf (73)))) (.branch 62 (.branch 61 (.leaf (74)) (.leaf (69))) (.branch 63 (.leaf (70)) (.leaf (77)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (78)) (.leaf (72))) (.branch 67 (.leaf (81)) (.leaf (83)))) (.branch 70 (.branch 69 (.leaf (41)) (.leaf (86))) (.branch 71 (.leaf (87)) (.leaf (43))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (90)) (.leaf (84))) (.branch 75 (.leaf (85)) (.leaf (93)))) (.branch 78 (.branch 77 (.leaf (95)) (.leaf (88))) (.branch 79 (.leaf (89)) (.leaf (96)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (98)) (.leaf (91))) (.branch 83 (.leaf (101)) (.leaf (48)))) (.branch 86 (.branch 85 (.leaf (102)) (.leaf (103))) (.branch 87 (.leaf (50)) (.leaf (51))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (106)) (.leaf (107))) (.branch 91 (.leaf (53)) (.leaf (110)))) (.branch 94 (.branch 93 (.leaf (82)) (.leaf (104))) (.branch 95 (.leaf (113)) (.leaf (105))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (108)) (.leaf (114))) (.branch 99 (.leaf (109)) (.leaf (115)))) (.branch 102 (.branch 101 (.leaf (99)) (.leaf (111))) (.branch 103 (.leaf (59)) (.leaf (60))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (118)) (.leaf (120))) (.branch 107 (.leaf (63)) (.leaf (64)))) (.branch 110 (.branch 109 (.leaf (121)) (.leaf (123))) (.branch 111 (.leaf (66)) (.leaf (92)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (125)) (.leaf (119))) (.branch 115 (.leaf (122)) (.leaf (124)))) (.branch 118 (.branch 117 (.leaf (112)) (.leaf (116))) (.branch 119 (.leaf (75)) (.leaf (127))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (76)) (.leaf (79))) (.branch 123 (.leaf (126)) (.leaf (80)))) (.branch 126 (.branch 125 (.leaf (100)) (.leaf (117))) (.branch 127 (.leaf (97)) (.leaf (94)))))))))
noncomputable def originalS (p : Fin 128) : Fin 128 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (10))) (.branch 7 (.leaf (12)) (.leaf (13))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (15)) (.leaf (16))) (.branch 11 (.leaf (17)) (.leaf (18)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (7))) (.branch 15 (.leaf (9)) (.leaf (22)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (5))) (.branch 19 (.leaf (3)) (.leaf (24)))) (.branch 22 (.branch 21 (.leaf (26)) (.leaf (23))) (.branch 23 (.leaf (28)) (.leaf (0))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (30)) (.leaf (31))) (.branch 27 (.leaf (21)) (.leaf (32)))) (.branch 30 (.branch 29 (.leaf (29)) (.leaf (11))) (.branch 31 (.leaf (35)) (.leaf (37))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (38)) (.leaf (39))) (.branch 35 (.leaf (25)) (.leaf (41)))) (.branch 38 (.branch 37 (.leaf (19)) (.leaf (43))) (.branch 39 (.leaf (45)) (.leaf (47))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (48)) (.leaf (50))) (.branch 43 (.leaf (51)) (.leaf (53)))) (.branch 46 (.branch 45 (.leaf (33)) (.leaf (55))) (.branch 47 (.leaf (27)) (.leaf (57)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (59)) (.leaf (60))) (.branch 51 (.leaf (62)) (.leaf (63)))) (.branch 54 (.branch 53 (.leaf (64)) (.leaf (66))) (.branch 55 (.leaf (67)) (.leaf (69))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (70)) (.leaf (72))) (.branch 59 (.leaf (34)) (.leaf (74)))) (.branch 62 (.branch 61 (.leaf (75)) (.leaf (76))) (.branch 63 (.leaf (36)) (.leaf (78)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (79)) (.leaf (80))) (.branch 67 (.leaf (82)) (.leaf (84)))) (.branch 70 (.branch 69 (.leaf (85)) (.leaf (87))) (.branch 71 (.leaf (88)) (.leaf (89))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (91)) (.leaf (92))) (.branch 75 (.leaf (40)) (.leaf (94)))) (.branch 78 (.branch 77 (.leaf (95)) (.leaf (86))) (.branch 79 (.leaf (42)) (.leaf (97)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (99)) (.leaf (100))) (.branch 83 (.leaf (58)) (.leaf (44)))) (.branch 86 (.branch 85 (.leaf (103)) (.leaf (104))) (.branch 87 (.leaf (105)) (.leaf (46))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (107)) (.leaf (108))) (.branch 91 (.leaf (109)) (.leaf (111)))) (.branch 94 (.branch 93 (.leaf (112)) (.leaf (102))) (.branch 95 (.leaf (96)) (.leaf (49))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (106)) (.leaf (93))) (.branch 99 (.leaf (52)) (.leaf (65)))) (.branch 102 (.branch 101 (.leaf (116)) (.leaf (117))) (.branch 103 (.leaf (101)) (.leaf (54))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (119)) (.leaf (120))) (.branch 107 (.leaf (61)) (.leaf (56)))) (.branch 110 (.branch 109 (.leaf (122)) (.leaf (124))) (.branch 111 (.leaf (115)) (.leaf (83)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (123)) (.leaf (126))) (.branch 115 (.leaf (127)) (.leaf (125)))) (.branch 118 (.branch 117 (.leaf (81)) (.leaf (98))) (.branch 119 (.leaf (73)) (.leaf (121))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (68)) (.leaf (77))) (.branch 123 (.leaf (118)) (.leaf (71)))) (.branch 126 (.branch 125 (.leaf (90)) (.leaf (110))) (.branch 127 (.leaf (113)) (.leaf (114)))))))))
noncomputable def originalT (p : Fin 128) : Fin 128 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 64) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (3))) (.branch 15 (.leaf (4)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (9)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 21 (.leaf (12)) (.leaf (7))) (.branch 23 (.leaf (8)) (.leaf (10))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (13)) (.leaf (14))) (.branch 27 (.leaf (15)) (.leaf (11)))) (.branch 30 (.branch 29 (.leaf (12)) (.leaf (15))) (.branch 31 (.leaf (16)) (.leaf (17))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (13)) (.leaf (14))) (.branch 35 (.leaf (18)) (.leaf (19)))) (.branch 38 (.branch 37 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (16)) (.leaf (17))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (22)) (.leaf (23))) (.branch 43 (.leaf (24)) (.leaf (25)))) (.branch 46 (.branch 45 (.leaf (18)) (.leaf (19))) (.branch 47 (.leaf (20)) (.leaf (21)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (26)) (.leaf (27))) (.branch 51 (.leaf (28)) (.leaf (29)))) (.branch 54 (.branch 53 (.leaf (30)) (.leaf (31))) (.branch 55 (.leaf (22)) (.leaf (23))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (24)) (.leaf (25))) (.branch 59 (.leaf (32)) (.leaf (33)))) (.branch 62 (.branch 61 (.leaf (34)) (.leaf (35))) (.branch 63 (.leaf (36)) (.leaf (37)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (38)) (.leaf (39))) (.branch 67 (.leaf (40)) (.leaf (26)))) (.branch 70 (.branch 69 (.leaf (27)) (.leaf (28))) (.branch 71 (.leaf (29)) (.leaf (30))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (31)) (.leaf (41))) (.branch 75 (.leaf (42)) (.leaf (43)))) (.branch 78 (.branch 77 (.leaf (44)) (.leaf (45))) (.branch 79 (.leaf (46)) (.leaf (47)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (48)) (.leaf (49))) (.branch 83 (.leaf (50)) (.leaf (32)))) (.branch 86 (.branch 85 (.leaf (33)) (.leaf (34))) (.branch 87 (.leaf (35)) (.leaf (36))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (37)) (.leaf (38))) (.branch 91 (.leaf (39)) (.leaf (40)))) (.branch 94 (.branch 93 (.leaf (51)) (.leaf (52))) (.branch 95 (.leaf (53)) (.leaf (54))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (55)) (.leaf (56))) (.branch 99 (.leaf (57)) (.leaf (58)))) (.branch 102 (.branch 101 (.leaf (59)) (.leaf (51))) (.branch 103 (.leaf (41)) (.leaf (42))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (43)) (.leaf (44))) (.branch 107 (.leaf (45)) (.leaf (46)))) (.branch 110 (.branch 109 (.leaf (47)) (.leaf (48))) (.branch 111 (.leaf (49)) (.leaf (50)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (60)) (.leaf (61))) (.branch 115 (.leaf (62)) (.leaf (59)))) (.branch 118 (.branch 117 (.leaf (63)) (.leaf (60))) (.branch 119 (.leaf (52)) (.leaf (53))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (54)) (.leaf (55))) (.branch 123 (.leaf (56)) (.leaf (57)))) (.branch 126 (.branch 125 (.leaf (58)) (.leaf (63))) (.branch 127 (.leaf (62)) (.leaf (61)))))))))
noncomputable def projection (p : Fin 128) : Fin 64 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 128) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (6))) (.branch 7 (.leaf (9)) (.leaf (11))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (16))) (.branch 11 (.leaf (18)) (.leaf (19)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (24))) (.branch 15 (.leaf (25)) (.leaf (26)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (30)) (.leaf (31))) (.branch 19 (.leaf (34)) (.leaf (35)))) (.branch 22 (.branch 21 (.leaf (36)) (.leaf (37))) (.branch 23 (.leaf (40)) (.leaf (41))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (42)) (.leaf (43))) (.branch 27 (.leaf (48)) (.leaf (49)))) (.branch 30 (.branch 29 (.leaf (50)) (.leaf (51))) (.branch 31 (.leaf (52)) (.leaf (53))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (58)) (.leaf (59))) (.branch 35 (.leaf (60)) (.leaf (61)))) (.branch 38 (.branch 37 (.leaf (62)) (.leaf (63))) (.branch 39 (.leaf (64)) (.leaf (65))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (66)) (.leaf (73))) (.branch 43 (.leaf (74)) (.leaf (75)))) (.branch 46 (.branch 45 (.leaf (76)) (.leaf (77))) (.branch 47 (.leaf (78)) (.leaf (79)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (80)) (.leaf (81))) (.branch 51 (.leaf (82)) (.leaf (92)))) (.branch 54 (.branch 53 (.leaf (93)) (.leaf (94))) (.branch 55 (.leaf (95)) (.leaf (96))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (97)) (.leaf (98))) (.branch 59 (.leaf (99)) (.leaf (100)))) (.branch 62 (.branch 61 (.leaf (112)) (.leaf (113))) (.branch 63 (.leaf (114)) (.leaf (116))))))))
noncomputable def representative (p : Fin 64) : Fin 128 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (7))) (.branch 7 (.leaf (3)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (11)) (.leaf (10))) (.branch 11 (.leaf (9)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (14)) (.leaf (15))) (.branch 15 (.leaf (12)) (.leaf (13)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (18)) (.leaf (20))) (.branch 19 (.leaf (16)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (17)) (.leaf (24))) (.branch 23 (.leaf (19)) (.leaf (27))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (30))) (.branch 27 (.leaf (32)) (.leaf (23)))) (.branch 30 (.branch 29 (.leaf (35)) (.leaf (36))) (.branch 31 (.leaf (25)) (.leaf (39))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (26)) (.leaf (41))) (.branch 35 (.leaf (42)) (.leaf (28)))) (.branch 38 (.branch 37 (.leaf (29)) (.leaf (45))) (.branch 39 (.leaf (46)) (.leaf (31))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (49)) (.leaf (33))) (.branch 43 (.leaf (34)) (.leaf (52)))) (.branch 46 (.branch 45 (.leaf (54)) (.leaf (37))) (.branch 47 (.leaf (38)) (.leaf (55)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (57)) (.leaf (40))) (.branch 51 (.leaf (51)) (.leaf (50)))) (.branch 54 (.branch 53 (.leaf (43)) (.leaf (61))) (.branch 55 (.leaf (44)) (.leaf (47))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (62)) (.leaf (48))) (.branch 59 (.leaf (59)) (.leaf (58)))) (.branch 62 (.branch 61 (.leaf (63)) (.leaf (53))) (.branch 63 (.leaf (56)) (.leaf (60))))))))
noncomputable def S (p : Fin 64) : Fin 64 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (8))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (4))) (.branch 11 (.leaf (0)) (.leaf (13)))) (.branch 14 (.branch 13 (.leaf (15)) (.leaf (16))) (.branch 15 (.leaf (17)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (19)) (.leaf (21))) (.branch 19 (.leaf (14)) (.leaf (23)))) (.branch 22 (.branch 21 (.leaf (11)) (.leaf (25))) (.branch 23 (.leaf (26)) (.leaf (28))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (29)) (.leaf (31))) (.branch 27 (.leaf (33)) (.leaf (34)))) (.branch 30 (.branch 29 (.leaf (36)) (.leaf (37))) (.branch 31 (.leaf (38)) (.leaf (40))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (18)) (.leaf (42))) (.branch 35 (.leaf (43)) (.leaf (44)))) (.branch 38 (.branch 37 (.leaf (20)) (.leaf (46))) (.branch 39 (.leaf (47)) (.leaf (48))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (50)) (.leaf (51))) (.branch 43 (.leaf (22)) (.leaf (53)))) (.branch 46 (.branch 45 (.leaf (54)) (.leaf (35))) (.branch 47 (.leaf (24)) (.leaf (56)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (58)) (.leaf (59))) (.branch 51 (.leaf (32)) (.leaf (60)))) (.branch 54 (.branch 53 (.leaf (41)) (.leaf (55))) (.branch 55 (.leaf (27)) (.leaf (45))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (52)) (.leaf (30))) (.branch 59 (.leaf (39)) (.leaf (63)))) (.branch 62 (.branch 61 (.leaf (57)) (.leaf (62))) (.branch 63 (.leaf (61)) (.leaf (49))))))))
noncomputable def T (p : Fin 64) : Fin 64 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (10)) (.leaf (3))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (15))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (20)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (11))) (.branch 15 (.leaf (18)) (.leaf (12)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (13)) (.leaf (14))) (.branch 19 (.leaf (32)) (.leaf (16)))) (.branch 22 (.branch 21 (.leaf (36)) (.leaf (17))) (.branch 23 (.leaf (42)) (.leaf (19))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (46)) (.leaf (21))) (.branch 27 (.leaf (22)) (.leaf (54)))) (.branch 30 (.branch 29 (.leaf (23)) (.leaf (24))) (.branch 31 (.leaf (57)) (.leaf (25))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (50)) (.leaf (26))) (.branch 35 (.leaf (27)) (.leaf (45)))) (.branch 38 (.branch 37 (.leaf (28)) (.leaf (29))) (.branch 39 (.leaf (30)) (.leaf (58))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (31)) (.leaf (52))) (.branch 43 (.leaf (33)) (.leaf (34)))) (.branch 46 (.branch 45 (.leaf (35)) (.leaf (55))) (.branch 47 (.leaf (37)) (.leaf (38)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (39)) (.leaf (63))) (.branch 51 (.leaf (40)) (.leaf (41)))) (.branch 54 (.branch 53 (.leaf (56)) (.leaf (43))) (.branch 55 (.leaf (44)) (.leaf (53))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (47)) (.leaf (60))) (.branch 59 (.leaf (48)) (.leaf (49)))) (.branch 62 (.branch 61 (.leaf (51)) (.leaf (62))) (.branch 63 (.leaf (61)) (.leaf (59))))))))
noncomputable def Ti (p : Fin 64) : Fin 64 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 64) : Fin 64 := T (S p)
theorem quotient_relations : (∀ p : Fin 64, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 128, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 128, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 64, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 64)) := [[0,3,9],[1,2,6],[4,5,10],[7,8,13],[11,12,17],[14,15,16],[18,19,26],[20,21,29],[22,23,34],[24,25,38],[27,28,44],[30,31,48],[32,33,51],[35,36,37],[39,40,59],[41,42,43],[45,46,47],[49,50,60],[52,53,62],[54],[55,56,61],[57,58,63]]
noncomputable def verticesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (5)) (.leaf (9))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (2))) (.branch 11 (.leaf (8)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (13)) (.leaf (11))) (.branch 15 (.leaf (15)) (.leaf (16)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (17)) (.leaf (14))) (.branch 19 (.leaf (18)) (.leaf (19)))) (.branch 22 (.branch 21 (.leaf (21)) (.leaf (22))) (.branch 23 (.leaf (24)) (.leaf (25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (27)) (.leaf (28))) (.branch 27 (.leaf (20)) (.leaf (30)))) (.branch 30 (.branch 29 (.leaf (31)) (.leaf (23))) (.branch 31 (.leaf (33)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (36)) (.leaf (37))) (.branch 35 (.leaf (26)) (.leaf (39)))) (.branch 38 (.branch 37 (.leaf (40)) (.leaf (41))) (.branch 39 (.leaf (29)) (.leaf (42))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (43)) (.leaf (45))) (.branch 43 (.leaf (46)) (.leaf (47)))) (.branch 46 (.branch 45 (.leaf (32)) (.leaf (48))) (.branch 47 (.leaf (49)) (.leaf (50)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (35)) (.leaf (51))) (.branch 51 (.leaf (52)) (.leaf (38)))) (.branch 54 (.branch 53 (.leaf (54)) (.leaf (55))) (.branch 55 (.leaf (57)) (.leaf (58))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (59)) (.leaf (61))) (.branch 59 (.leaf (62)) (.leaf (44)))) (.branch 62 (.branch 61 (.leaf (53)) (.leaf (60))) (.branch 63 (.leaf (56)) (.leaf (63))))))))
noncomputable def verticesIndex (p : Fin 64) : Fin 64 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (9)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (7))) (.branch 11 (.leaf (8)) (.leaf (13)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (12))) (.branch 15 (.leaf (17)) (.leaf (14)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (15)) (.leaf (16))) (.branch 19 (.leaf (18)) (.leaf (19)))) (.branch 22 (.branch 21 (.leaf (26)) (.leaf (20))) (.branch 23 (.leaf (21)) (.leaf (29))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (22)) (.leaf (23))) (.branch 27 (.leaf (34)) (.leaf (24)))) (.branch 30 (.branch 29 (.leaf (25)) (.leaf (38))) (.branch 31 (.leaf (27)) (.leaf (28))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (44)) (.leaf (30))) (.branch 35 (.leaf (31)) (.leaf (48)))) (.branch 38 (.branch 37 (.leaf (32)) (.leaf (33))) (.branch 39 (.leaf (51)) (.leaf (35))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (36)) (.leaf (37))) (.branch 43 (.leaf (39)) (.leaf (40)))) (.branch 46 (.branch 45 (.leaf (59)) (.leaf (41))) (.branch 47 (.leaf (42)) (.leaf (43)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (45)) (.leaf (46))) (.branch 51 (.leaf (47)) (.leaf (49)))) (.branch 54 (.branch 53 (.leaf (50)) (.leaf (60))) (.branch 55 (.leaf (52)) (.leaf (53))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (62)) (.leaf (54))) (.branch 59 (.leaf (55)) (.leaf (56)))) (.branch 62 (.branch 61 (.leaf (61)) (.leaf (57))) (.branch 63 (.leaf (58)) (.leaf (63))))))))
noncomputable def verticesBack (p : Fin 64) : Fin 64 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 64, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 64 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 64, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 64)) := [[0,1],[2,4],[3,6],[5,7],[8,11],[9,10],[12,14],[13,15],[16,18],[17,20],[19,22],[21,24],[23,27],[25,30],[26,32],[28,35],[29,36],[31,39],[33,41],[34,42],[37,45],[38,46],[40,49],[43,52],[44,54],[47,55],[48,57],[50,51],[53,61],[56,62],[58,59],[60,63]]
noncomputable def edgesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (8)) (.leaf (10))) (.branch 11 (.leaf (11)) (.leaf (9)))) (.branch 14 (.branch 13 (.leaf (12)) (.leaf (14))) (.branch 15 (.leaf (13)) (.leaf (15)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (16)) (.leaf (18))) (.branch 19 (.leaf (17)) (.leaf (20)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (22))) (.branch 23 (.leaf (21)) (.leaf (24))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (23)) (.leaf (26))) (.branch 27 (.leaf (28)) (.leaf (25)))) (.branch 30 (.branch 29 (.leaf (30)) (.leaf (32))) (.branch 31 (.leaf (27)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (29)) (.leaf (36))) (.branch 35 (.leaf (38)) (.leaf (31)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (40))) (.branch 39 (.leaf (42)) (.leaf (35))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (44)) (.leaf (37))) (.branch 43 (.leaf (39)) (.leaf (46)))) (.branch 46 (.branch 45 (.leaf (48)) (.leaf (41))) (.branch 47 (.leaf (43)) (.leaf (50)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (52)) (.leaf (45))) (.branch 51 (.leaf (54)) (.leaf (55)))) (.branch 54 (.branch 53 (.leaf (47)) (.leaf (56))) (.branch 55 (.leaf (49)) (.leaf (51))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (58)) (.leaf (53))) (.branch 59 (.leaf (60)) (.leaf (61)))) (.branch 62 (.branch 61 (.leaf (62)) (.leaf (57))) (.branch 63 (.leaf (59)) (.leaf (63))))))))
noncomputable def edgesIndex (p : Fin 64) : Fin 64 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (8)) (.leaf (11))) (.branch 11 (.leaf (9)) (.leaf (10)))) (.branch 14 (.branch 13 (.leaf (12)) (.leaf (14))) (.branch 15 (.leaf (13)) (.leaf (15)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (16)) (.leaf (18))) (.branch 19 (.leaf (17)) (.leaf (20)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (22))) (.branch 23 (.leaf (21)) (.leaf (24))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (23)) (.leaf (27))) (.branch 27 (.leaf (25)) (.leaf (30)))) (.branch 30 (.branch 29 (.leaf (26)) (.leaf (32))) (.branch 31 (.leaf (28)) (.leaf (35))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (29)) (.leaf (36))) (.branch 35 (.leaf (31)) (.leaf (39)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (41))) (.branch 39 (.leaf (34)) (.leaf (42))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (45))) (.branch 43 (.leaf (38)) (.leaf (46)))) (.branch 46 (.branch 45 (.leaf (40)) (.leaf (49))) (.branch 47 (.leaf (43)) (.leaf (52)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (44)) (.leaf (54))) (.branch 51 (.leaf (47)) (.leaf (55)))) (.branch 54 (.branch 53 (.leaf (48)) (.leaf (57))) (.branch 55 (.leaf (50)) (.leaf (51))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (53)) (.leaf (61))) (.branch 59 (.leaf (56)) (.leaf (62)))) (.branch 62 (.branch 61 (.leaf (58)) (.leaf (59))) (.branch 63 (.leaf (60)) (.leaf (63))))))))
noncomputable def edgesBack (p : Fin 64) : Fin 64 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 64, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 64 := by decide +kernel
theorem edges_partition : ∀ p : Fin 64, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 64)) := [[0,2,5,8,12,15,7,10],[1,3],[4,6,9],[11,13,16,19,23,28,36,20],[14,17,21,25,31,40,50,32,18],[22,26,33,42],[24,29,37,46],[27,34,43,53,55,45,35,44,54],[30,38,47,56,52,41,51,60,57],[39,48,58],[49,59,63],[61,62]]
noncomputable def facesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (8))) (.branch 3 (.leaf (1)) (.leaf (9)))) (.branch 6 (.branch 5 (.leaf (10)) (.leaf (2))) (.branch 7 (.leaf (11)) (.leaf (6))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (12))) (.branch 11 (.leaf (7)) (.leaf (13)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (14))) (.branch 15 (.leaf (21)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (15)) (.leaf (22))) (.branch 19 (.leaf (29)) (.leaf (16)))) (.branch 22 (.branch 21 (.leaf (20)) (.leaf (23))) (.branch 23 (.leaf (30)) (.leaf (17))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (34)) (.leaf (24))) (.branch 27 (.leaf (31)) (.leaf (38)))) (.branch 30 (.branch 29 (.leaf (18)) (.leaf (35))) (.branch 31 (.leaf (47)) (.leaf (25))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (28)) (.leaf (32))) (.branch 35 (.leaf (39)) (.leaf (44)))) (.branch 38 (.branch 37 (.leaf (19)) (.leaf (36))) (.branch 39 (.leaf (48)) (.leaf (56))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (26)) (.leaf (52))) (.branch 43 (.leaf (33)) (.leaf (40)))) (.branch 46 (.branch 45 (.leaf (45)) (.leaf (43))) (.branch 47 (.leaf (37)) (.leaf (49)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (57)) (.leaf (59))) (.branch 51 (.leaf (27)) (.leaf (53)))) (.branch 54 (.branch 53 (.leaf (51)) (.leaf (41))) (.branch 55 (.leaf (46)) (.leaf (42))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (50)) (.leaf (55))) (.branch 59 (.leaf (58)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (54)) (.leaf (62))) (.branch 63 (.leaf (63)) (.leaf (61))))))))
noncomputable def facesIndex (p : Fin 64) : Fin 64 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (12)) (.leaf (15))) (.branch 7 (.leaf (7)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (4)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (9)) (.leaf (11))) (.branch 15 (.leaf (13)) (.leaf (16)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (19)) (.leaf (23))) (.branch 19 (.leaf (28)) (.leaf (36)))) (.branch 22 (.branch 21 (.leaf (20)) (.leaf (14))) (.branch 23 (.leaf (17)) (.leaf (21))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (25)) (.leaf (31))) (.branch 27 (.leaf (40)) (.leaf (50)))) (.branch 30 (.branch 29 (.leaf (32)) (.leaf (18))) (.branch 31 (.leaf (22)) (.leaf (26))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (33)) (.leaf (42))) (.branch 35 (.leaf (24)) (.leaf (29)))) (.branch 38 (.branch 37 (.leaf (37)) (.leaf (46))) (.branch 39 (.leaf (27)) (.leaf (34))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (43)) (.leaf (53))) (.branch 43 (.leaf (55)) (.leaf (45)))) (.branch 46 (.branch 45 (.leaf (35)) (.leaf (44))) (.branch 47 (.leaf (54)) (.leaf (30)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (38)) (.leaf (47))) (.branch 51 (.leaf (56)) (.leaf (52)))) (.branch 54 (.branch 53 (.leaf (41)) (.leaf (51))) (.branch 55 (.leaf (60)) (.leaf (57))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (39)) (.leaf (48))) (.branch 59 (.leaf (58)) (.leaf (49)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (63))) (.branch 63 (.leaf (61)) (.leaf (62))))))))
noncomputable def facesBack (p : Fin 64) : Fin 64 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 64, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 64 := by decide +kernel
theorem faces_partition : ∀ p : Fin 64, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [8,2,3,8,9,4,4,9,9,3,3,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 22 - 32 + 12 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 1 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨2,-1,1,0⟩))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (⟨-1,-3,0,-1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 11 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨-3,1,-1,0⟩)))) (.branch 14 (.branch 13 (.leaf (⟨1,4,0,1⟩)) (.leaf (⟨-3,-2,-1,-1⟩))) (.branch 15 (.leaf (⟨4,-1,1,0⟩)) (.leaf (⟨-1,-5,0,-1⟩)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (⟨-5,-4,-1,-1⟩)) (.leaf (⟨4,3,1,1⟩))) (.branch 19 (.leaf (⟨-4,5,-1,1⟩)) (.leaf (⟨5,9,1,2⟩)))) (.branch 22 (.branch 21 (.leaf (⟨3,-4,1,-1⟩)) (.leaf (⟨-4,-7,-1,-2⟩))) (.branch 23 (.leaf (⟨9,-5,2,-1⟩)) (.leaf (⟨-5,-14,-1,-3⟩))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (⟨-7,4,-2,1⟩)) (.leaf (⟨4,11,1,3⟩))) (.branch 27 (.leaf (⟨9,4,2,1⟩)) (.leaf (⟨-13,-3,-4,-1⟩)))) (.branch 30 (.branch 29 (.leaf (⟨3,-10,1,-3⟩)) (.leaf (⟨-7,-3,-2,-1⟩))) (.branch 31 (.leaf (⟨11,-4,3,-1⟩)) (.leaf (⟨-4,-15,-1,-4⟩))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (⟨4,-9,1,-2⟩)) (.leaf (⟨-9,-13,-2,-3⟩))) (.branch 35 (.leaf (⟨-14,-9,-3,-2⟩)) (.leaf (⟨10,3,3,1⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-3,7,-1,2⟩)) (.leaf (⟨7,10,2,3⟩))) (.branch 39 (.leaf (⟨11,7,3,2⟩)) (.leaf (⟨-15,4,-4,1⟩))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (⟨4,19,1,5⟩)) (.leaf (⟨23,9,5,2⟩))) (.branch 43 (.leaf (⟨-9,14,-2,3⟩)) (.leaf (⟨14,23,3,5⟩)))) (.branch 46 (.branch 45 (.leaf (⟨-10,-13,-3,-4⟩)) (.leaf (⟨-18,-7,-5,-2⟩))) (.branch 47 (.leaf (⟨7,-11,2,-3⟩)) (.leaf (⟨-11,-18,-3,-5⟩)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (⟨-15,-11,-4,-3⟩)) (.leaf (⟨17,4,4,1⟩))) (.branch 51 (.leaf (⟨-4,13,-1,3⟩)) (.leaf (⟨-13,-4,-3,-1⟩)))) (.branch 54 (.branch 53 (.leaf (⟨23,-14,5,-3⟩)) (.leaf (⟨-14,-37,-3,-8⟩))) (.branch 55 (.leaf (⟨-13,10,-4,3⟩)) (.leaf (⟨-18,11,-5,3⟩))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (⟨11,29,3,8⟩)) (.leaf (⟨-11,15,-3,4⟩))) (.branch 59 (.leaf (⟨15,26,4,7⟩)) (.leaf (⟨19,15,5,4⟩)))) (.branch 62 (.branch 61 (.leaf (⟨13,17,3,4⟩)) (.leaf (⟨29,18,8,5⟩))) (.branch 63 (.leaf (⟨-37,-23,-8,-5⟩)) (.leaf (⟨26,11,7,3⟩))))))))
noncomputable def liftMatrix (p : Fin 64) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 64) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],6⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],7⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],10⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],11⟩,⟨⟨1,4,0,1⟩,[.t (4)],12⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],13⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],14⟩,⟨⟨-1,-5,0,-1⟩,[.t (5)],15⟩,⟨⟨-5,-4,-1,-1⟩,[.t (5),.s,.t (1)],16⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],17⟩,⟨⟨-4,5,-1,1⟩,[.t (4),.s,.t (-1)],18⟩,⟨⟨5,9,1,2⟩,[.t (5),.s,.t (2)],19⟩,⟨⟨3,-4,1,-1⟩,[.t (3),.s,.t (-1)],20⟩,⟨⟨-4,-7,-1,-2⟩,[.t (4),.s,.t (2)],21⟩,⟨⟨9,-5,2,-1⟩,[.t (4),.s,.t (-2),.s,.t (-1)],22⟩,⟨⟨-5,-14,-1,-3⟩,[.t (5),.s,.t (3)],23⟩,⟨⟨-7,4,-2,1⟩,[.t (3),.s,.t (-2),.s,.t (-1)],24⟩,⟨⟨4,11,1,3⟩,[.t (4),.s,.t (3)],25⟩,⟨⟨9,4,2,1⟩,[.t (4),.s,.t (-2),.s,.t (0)],26⟩,⟨⟨-13,-3,-4,-1⟩,[.t (3),.s,.t (-4),.s,.t (0)],27⟩,⟨⟨3,-10,1,-3⟩,[.t (3),.s,.t (-3)],28⟩,⟨⟨-7,-3,-2,-1⟩,[.t (3),.s,.t (-2),.s,.t (0)],29⟩,⟨⟨11,-4,3,-1⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-1)],30⟩,⟨⟨-4,-15,-1,-4⟩,[.t (4),.s,.t (4)],31⟩,⟨⟨4,-9,1,-2⟩,[.t (4),.s,.t (-2)],32⟩,⟨⟨-9,-13,-2,-3⟩,[.t (4),.s,.t (-2),.s,.t (1)],33⟩,⟨⟨-14,-9,-3,-2⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (0)],34⟩,⟨⟨10,3,3,1⟩,[.t (3),.s,.t (-3),.s,.t (0)],35⟩,⟨⟨-3,7,-1,2⟩,[.t (3),.s,.t (-2)],36⟩,⟨⟨7,10,2,3⟩,[.t (3),.s,.t (-2),.s,.t (1)],37⟩,⟨⟨11,7,3,2⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (0)],38⟩,⟨⟨-15,4,-4,1⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],39⟩,⟨⟨4,19,1,5⟩,[.t (4),.s,.t (5)],40⟩,⟨⟨23,9,5,2⟩,[.t (4),.s,.t (-2),.s,.t (-3),.s,.t (0)],41⟩,⟨⟨-9,14,-2,3⟩,[.t (4),.s,.t (-2),.s,.t (-2)],42⟩,⟨⟨14,23,3,5⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (1)],43⟩,⟨⟨-10,-13,-3,-4⟩,[.t (3),.s,.t (-3),.s,.t (1)],44⟩,⟨⟨-18,-7,-5,-2⟩,[.t (3),.s,.t (-2),.s,.t (-3),.s,.t (0)],45⟩,⟨⟨7,-11,2,-3⟩,[.t (3),.s,.t (-2),.s,.t (-2)],46⟩,⟨⟨-11,-18,-3,-5⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (1)],47⟩,⟨⟨-15,-11,-4,-3⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],48⟩,⟨⟨17,4,4,1⟩,[.t (4),.s,.t (-4),.s,.t (0)],49⟩,⟨⟨-4,13,-1,3⟩,[.t (4),.s,.t (-3)],50⟩,⟨⟨-13,-4,-3,-1⟩,[.t (4),.s,.t (-3),.s,.t (0)],51⟩,⟨⟨23,-14,5,-3⟩,[.t (4),.s,.t (-2),.s,.t (-3),.s,.t (-1)],52⟩,⟨⟨-14,-37,-3,-8⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (2)],53⟩,⟨⟨-13,10,-4,3⟩,[.t (3),.s,.t (-4),.s,.t (-1)],54⟩,⟨⟨-18,11,-5,3⟩,[.t (3),.s,.t (-2),.s,.t (-3),.s,.t (-1)],55⟩,⟨⟨11,29,3,8⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (2)],56⟩,⟨⟨-11,15,-3,4⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2)],57⟩,⟨⟨15,26,4,7⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],58⟩,⟨⟨19,15,5,4⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],59⟩,⟨⟨13,17,3,4⟩,[.t (4),.s,.t (-3),.s,.t (1)],60⟩,⟨⟨29,18,8,5⟩,[.t (3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],61⟩,⟨⟨-37,-23,-8,-5⟩,[.t (4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],62⟩,⟨⟨26,11,7,3⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],63⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 64 ∧ ((List.finRange 64).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 64) := [⟨9,2,⟨⟨2,3,1,2⟩,[.t (2),.s,.t (2)],0⟩⟩,⟨3,1,⟨⟨-1,0,-2,-1⟩,[.t (0),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨6,1,⟨⟨-1,0,2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨10,2,⟨⟨2,-3,-1,2⟩,[.t (-2),.s,.t (-2)],0⟩⟩,⟨13,3,⟨⟨6,-13,1,-2⟩,[.t (6),.s,.t (-2)],0⟩⟩,⟨27,4,⟨⟨-34,107,-7,22⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨54,-3,⟨⟨122,-399,37,-121⟩,[.t (3),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨37,6,⟨⟨-57,196,-16,55⟩,[.t (3),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨45,6,⟨⟨55,-196,16,-57⟩,[.t (3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-4)],0⟩⟩,⟨61,8,⟨⟨297,-1072,64,-231⟩,[.t (4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-4)],0⟩⟩,⟨56,9,⟨⟨-295,1074,-64,233⟩,[.t (4),.s,.t (-2),.s,.t (-3),.s,.t (-5),.s,.t (-3),.s,.t (-4)],0⟩⟩,⟨63,11,⟨⟨-142,525,-33,122⟩,[.t (4),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-4)],0⟩⟩,⟨58,10,⟨⟨181,-675,48,-179⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-4),.s,.t (-4)],0⟩⟩,⟨59,10,⟨⟨-179,675,-48,181⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-5),.s,.t (-4)],0⟩⟩,⟨40,7,⟨⟨37,-144,9,-35⟩,[.t (4),.s,.t (-9),.s,.t (-4)],0⟩⟩,⟨49,7,⟨⟨-35,144,-9,37⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨60,11,⟨⟨122,-525,33,-142⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨33,5,⟨⟨-73,324,-16,71⟩,[.t (4),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨41,5,⟨⟨71,-324,16,-73⟩,[.t (4),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-5)],0⟩⟩,⟨62,9,⟨⟨233,-1074,64,-295⟩,[.t (3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-5)],0⟩⟩,⟨53,8,⟨⟨-231,1072,-64,297⟩,[.t (3),.s,.t (-2),.s,.t (-3),.s,.t (-5),.s,.t (-3),.s,.t (-5)],0⟩⟩,⟨23,4,⟨⟨22,-107,7,-34⟩,[.t (3),.s,.t (-7),.s,.t (-5)],0⟩⟩,⟨15,3,⟨⟨-2,13,-1,6⟩,[.t (2),.s,.t (-6)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(0,1),(1,1),(2,1),(3,1),(13,4),(10,3),(7,2),(18,5),(29,8),(11,3),(26,7),(15,4),(19,5),(4,1),(17,4),(13,3),(9,2),(23,5),(37,8),(14,3),(5,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end PSL2_17_c3

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
