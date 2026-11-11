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
namespace PSL2_17_c10
noncomputable def originalSData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (8))) (.branch 7 (.leaf (12)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (15)) (.leaf (14))) (.branch 11 (.leaf (18)) (.leaf (10)))) (.branch 14 (.branch 13 (.leaf (16)) (.leaf (21))) (.branch 15 (.leaf (23)) (.leaf (2)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (25)) (.leaf (27))) (.branch 19 (.leaf (24)) (.leaf (30)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (26))) (.branch 23 (.leaf (32)) (.leaf (4))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (11)) (.leaf (6))) (.branch 27 (.leaf (34)) (.leaf (33)))) (.branch 30 (.branch 29 (.leaf (36)) (.leaf (20))) (.branch 31 (.leaf (29)) (.leaf (38))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (35)) (.leaf (41))) (.branch 35 (.leaf (13)) (.leaf (44)))) (.branch 38 (.branch 37 (.leaf (42)) (.leaf (46))) (.branch 39 (.leaf (43)) (.leaf (48))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (45)) (.leaf (17))) (.branch 43 (.leaf (50)) (.leaf (52)))) (.branch 46 (.branch 45 (.leaf (22)) (.leaf (54))) (.branch 47 (.leaf (51)) (.leaf (56)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (53)) (.leaf (59))) (.branch 51 (.leaf (28)) (.leaf (62)))) (.branch 54 (.branch 53 (.leaf (31)) (.leaf (64))) (.branch 55 (.leaf (61)) (.leaf (66))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (63)) (.leaf (69))) (.branch 59 (.leaf (57)) (.leaf (65)))) (.branch 62 (.branch 61 (.leaf (72)) (.leaf (40))) (.branch 63 (.leaf (37)) (.leaf (75)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (39)) (.leaf (77))) (.branch 67 (.leaf (74)) (.leaf (79)))) (.branch 70 (.branch 69 (.leaf (70)) (.leaf (76))) (.branch 71 (.leaf (82)) (.leaf (83))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (78)) (.leaf (86))) (.branch 75 (.leaf (87)) (.leaf (47)))) (.branch 78 (.branch 77 (.leaf (58)) (.leaf (49))) (.branch 79 (.leaf (90)) (.leaf (88)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (93)) (.leaf (68))) (.branch 83 (.leaf (81)) (.leaf (89)))) (.branch 86 (.branch 85 (.leaf (95)) (.leaf (97))) (.branch 87 (.leaf (91)) (.leaf (55))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (99)) (.leaf (101))) (.branch 91 (.leaf (60)) (.leaf (92)))) (.branch 94 (.branch 93 (.leaf (73)) (.leaf (100))) (.branch 95 (.leaf (105)) (.leaf (102))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (107)) (.leaf (103))) (.branch 99 (.leaf (85)) (.leaf (67)))) (.branch 102 (.branch 101 (.leaf (109)) (.leaf (71))) (.branch 103 (.leaf (111)) (.leaf (98))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (108)) (.leaf (110))) (.branch 107 (.leaf (94)) (.leaf (112)))) (.branch 110 (.branch 109 (.leaf (117)) (.leaf (80))) (.branch 111 (.leaf (106)) (.leaf (84)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (118)) (.leaf (120))) (.branch 115 (.leaf (121)) (.leaf (123)))) (.branch 118 (.branch 117 (.leaf (124)) (.leaf (119))) (.branch 119 (.leaf (96)) (.leaf (104))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (126)) (.leaf (115))) (.branch 123 (.leaf (116)) (.leaf (114)))) (.branch 126 (.branch 125 (.leaf (127)) (.leaf (113))) (.branch 127 (.leaf (125)) (.leaf (122)))))))))
noncomputable def originalS (p : Fin 128) : Fin 128 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (10)) (.leaf (11))) (.branch 7 (.leaf (13)) (.leaf (14))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (16)) (.leaf (17))) (.branch 11 (.leaf (1)) (.leaf (19)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (22))) (.branch 15 (.leaf (24)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (26)) (.leaf (28))) (.branch 19 (.leaf (29)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (9)) (.leaf (31))) (.branch 23 (.leaf (32)) (.leaf (33))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (30))) (.branch 27 (.leaf (35)) (.leaf (3)))) (.branch 30 (.branch 29 (.leaf (37)) (.leaf (15))) (.branch 31 (.leaf (23)) (.leaf (39))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (40)) (.leaf (42))) (.branch 35 (.leaf (43)) (.leaf (44)))) (.branch 38 (.branch 37 (.leaf (45)) (.leaf (47))) (.branch 39 (.leaf (12)) (.leaf (49))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (41)) (.leaf (0))) (.branch 43 (.leaf (51)) (.leaf (53)))) (.branch 46 (.branch 45 (.leaf (54)) (.leaf (21))) (.branch 47 (.leaf (55)) (.leaf (57)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (58)) (.leaf (60))) (.branch 51 (.leaf (61)) (.leaf (63)))) (.branch 54 (.branch 53 (.leaf (25)) (.leaf (65))) (.branch 55 (.leaf (27)) (.leaf (67))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (68)) (.leaf (38))) (.branch 59 (.leaf (70)) (.leaf (71)))) (.branch 62 (.branch 61 (.leaf (73)) (.leaf (34))) (.branch 63 (.leaf (74)) (.leaf (76)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (69)) (.leaf (78))) (.branch 67 (.leaf (36)) (.leaf (80)))) (.branch 70 (.branch 69 (.leaf (56)) (.leaf (81))) (.branch 71 (.leaf (46)) (.leaf (84))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (85)) (.leaf (66))) (.branch 75 (.leaf (88)) (.leaf (82)))) (.branch 78 (.branch 77 (.leaf (52)) (.leaf (89))) (.branch 79 (.leaf (91)) (.leaf (92)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (94)) (.leaf (62))) (.branch 83 (.leaf (75)) (.leaf (48)))) (.branch 86 (.branch 85 (.leaf (96)) (.leaf (72))) (.branch 87 (.leaf (98)) (.leaf (50))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (100)) (.leaf (102))) (.branch 91 (.leaf (103)) (.leaf (87)))) (.branch 94 (.branch 93 (.leaf (97)) (.leaf (104))) (.branch 95 (.leaf (83)) (.leaf (106))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (108)) (.leaf (59))) (.branch 99 (.leaf (77)) (.leaf (86)))) (.branch 102 (.branch 101 (.leaf (110)) (.leaf (64))) (.branch 103 (.leaf (112)) (.leaf (90))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (113)) (.leaf (114))) (.branch 107 (.leaf (115)) (.leaf (116)))) (.branch 110 (.branch 109 (.leaf (79)) (.leaf (117))) (.branch 111 (.leaf (101)) (.leaf (105)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (119)) (.leaf (121))) (.branch 115 (.leaf (122)) (.leaf (124)))) (.branch 118 (.branch 117 (.leaf (125)) (.leaf (126))) (.branch 119 (.leaf (127)) (.leaf (99))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (118)) (.leaf (93))) (.branch 123 (.leaf (111)) (.leaf (109)))) (.branch 126 (.branch 125 (.leaf (95)) (.leaf (107))) (.branch 127 (.leaf (123)) (.leaf (120)))))))))
noncomputable def originalT (p : Fin 128) : Fin 128 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 64) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (9)) (.leaf (10))) (.branch 15 (.leaf (3)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (5)) (.leaf (11))) (.branch 19 (.leaf (8)) (.leaf (12)))) (.branch 22 (.branch 21 (.leaf (13)) (.leaf (14))) (.branch 23 (.leaf (15)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (7)) (.leaf (9))) (.branch 27 (.leaf (10)) (.leaf (16)))) (.branch 30 (.branch 29 (.leaf (17)) (.leaf (12))) (.branch 31 (.leaf (13)) (.leaf (18))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (19)) (.leaf (11))) (.branch 35 (.leaf (14)) (.leaf (15)))) (.branch 38 (.branch 37 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (24)) (.leaf (16))) (.branch 43 (.leaf (17)) (.leaf (18)))) (.branch 46 (.branch 45 (.leaf (19)) (.leaf (25))) (.branch 47 (.leaf (26)) (.leaf (27)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (28)) (.leaf (29))) (.branch 51 (.leaf (20)) (.leaf (21)))) (.branch 54 (.branch 53 (.leaf (22)) (.leaf (23))) (.branch 55 (.leaf (24)) (.leaf (30))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (31)) (.leaf (32))) (.branch 59 (.leaf (33)) (.leaf (34)))) (.branch 62 (.branch 61 (.leaf (35)) (.leaf (25))) (.branch 63 (.leaf (26)) (.leaf (27)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (28)) (.leaf (29))) (.branch 67 (.leaf (36)) (.leaf (37)))) (.branch 70 (.branch 69 (.leaf (38)) (.leaf (33))) (.branch 71 (.leaf (39)) (.leaf (40))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (41)) (.leaf (42))) (.branch 75 (.leaf (30)) (.leaf (31)))) (.branch 78 (.branch 77 (.leaf (32)) (.leaf (34))) (.branch 79 (.leaf (35)) (.leaf (43)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (44)) (.leaf (39))) (.branch 83 (.leaf (38)) (.leaf (45)))) (.branch 86 (.branch 85 (.leaf (46)) (.leaf (47))) (.branch 87 (.leaf (48)) (.leaf (36))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (37)) (.leaf (40))) (.branch 91 (.leaf (41)) (.leaf (42)))) (.branch 94 (.branch 93 (.leaf (48)) (.leaf (49))) (.branch 95 (.leaf (50)) (.leaf (51))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (52)) (.leaf (53))) (.branch 99 (.leaf (53)) (.leaf (43)))) (.branch 102 (.branch 101 (.leaf (44)) (.leaf (45))) (.branch 103 (.leaf (46)) (.leaf (47))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (54)) (.leaf (55))) (.branch 107 (.leaf (55)) (.leaf (56)))) (.branch 110 (.branch 109 (.leaf (57)) (.leaf (49))) (.branch 111 (.leaf (50)) (.leaf (51)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (52)) (.leaf (58))) (.branch 115 (.leaf (59)) (.leaf (59)))) (.branch 118 (.branch 117 (.leaf (60)) (.leaf (54))) (.branch 119 (.leaf (56)) (.leaf (57))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (61)) (.leaf (62))) (.branch 123 (.leaf (63)) (.leaf (62)))) (.branch 126 (.branch 125 (.leaf (63)) (.leaf (61))) (.branch 127 (.leaf (58)) (.leaf (60)))))))))
noncomputable def projection (p : Fin 128) : Fin 64 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 128) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (6))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (11)) (.leaf (12))) (.branch 11 (.leaf (13)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (19)) (.leaf (20))) (.branch 15 (.leaf (21)) (.leaf (22)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (27)) (.leaf (28))) (.branch 19 (.leaf (31)) (.leaf (32)))) (.branch 22 (.branch 21 (.leaf (36)) (.leaf (37))) (.branch 23 (.leaf (38)) (.leaf (39))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (40)) (.leaf (45))) (.branch 27 (.leaf (46)) (.leaf (47)))) (.branch 30 (.branch 29 (.leaf (48)) (.leaf (49))) (.branch 31 (.leaf (55)) (.leaf (56))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (57)) (.leaf (58))) (.branch 35 (.leaf (59)) (.leaf (60)))) (.branch 38 (.branch 37 (.leaf (66)) (.leaf (67))) (.branch 39 (.leaf (68)) (.leaf (70))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (71)) (.leaf (72))) (.branch 43 (.leaf (73)) (.leaf (79)))) (.branch 46 (.branch 45 (.leaf (80)) (.leaf (83))) (.branch 47 (.leaf (84)) (.leaf (85)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (86)) (.leaf (93))) (.branch 51 (.leaf (94)) (.leaf (95)))) (.branch 54 (.branch 53 (.leaf (96)) (.leaf (97))) (.branch 55 (.leaf (104)) (.leaf (105))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (107)) (.leaf (108))) (.branch 59 (.leaf (113)) (.leaf (114)))) (.branch 62 (.branch 61 (.leaf (116)) (.leaf (120))) (.branch 63 (.leaf (121)) (.leaf (122))))))))
noncomputable def representative (p : Fin 64) : Fin 128 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.leaf (8))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (5))) (.branch 11 (.leaf (14)) (.leaf (16)))) (.branch 14 (.branch 13 (.leaf (13)) (.leaf (12))) (.branch 15 (.leaf (10)) (.leaf (19)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (11)) (.leaf (20))) (.branch 19 (.leaf (22)) (.leaf (15)))) (.branch 22 (.branch 21 (.leaf (17)) (.leaf (26))) (.branch 23 (.leaf (18)) (.leaf (28))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (25)) (.leaf (24))) (.branch 27 (.leaf (21)) (.leaf (31)))) (.branch 30 (.branch 29 (.leaf (23)) (.leaf (34))) (.branch 31 (.leaf (36)) (.leaf (27))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (33)) (.leaf (32))) (.branch 35 (.leaf (29)) (.leaf (41)))) (.branch 38 (.branch 37 (.leaf (30)) (.leaf (43))) (.branch 39 (.leaf (39)) (.leaf (38))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (45)) (.leaf (35))) (.branch 43 (.leaf (48)) (.leaf (37)))) (.branch 46 (.branch 45 (.leaf (49)) (.leaf (40))) (.branch 47 (.leaf (51)) (.leaf (53)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (42)) (.leaf (44))) (.branch 51 (.leaf (55)) (.leaf (46)))) (.branch 54 (.branch 53 (.leaf (56)) (.leaf (47))) (.branch 55 (.leaf (57)) (.leaf (50))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (52)) (.leaf (54))) (.branch 59 (.leaf (61)) (.leaf (62)))) (.branch 62 (.branch 61 (.leaf (63)) (.leaf (58))) (.branch 63 (.leaf (59)) (.leaf (60))))))))
noncomputable def S (p : Fin 64) : Fin 64 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (10))) (.branch 7 (.leaf (11)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (13))) (.branch 11 (.leaf (15)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (6))) (.branch 15 (.leaf (18)) (.leaf (19)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (0)) (.leaf (21))) (.branch 19 (.leaf (23)) (.leaf (24)))) (.branch 22 (.branch 21 (.leaf (25)) (.leaf (27))) (.branch 23 (.leaf (9)) (.leaf (29))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (16)) (.leaf (14))) (.branch 27 (.leaf (30)) (.leaf (32)))) (.branch 30 (.branch 29 (.leaf (33)) (.leaf (35))) (.branch 31 (.leaf (37)) (.leaf (38))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (22)) (.leaf (39))) (.branch 35 (.leaf (40)) (.leaf (42)))) (.branch 38 (.branch 37 (.leaf (20)) (.leaf (44))) (.branch 39 (.leaf (31)) (.leaf (26))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (46)) (.leaf (47))) (.branch 43 (.leaf (36)) (.leaf (48)))) (.branch 46 (.branch 45 (.leaf (50)) (.leaf (28))) (.branch 47 (.leaf (52)) (.leaf (41)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (53)) (.leaf (54))) (.branch 51 (.leaf (45)) (.leaf (55)))) (.branch 54 (.branch 53 (.leaf (57)) (.leaf (34))) (.branch 55 (.leaf (58)) (.leaf (59))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (60)) (.leaf (43))) (.branch 59 (.leaf (62)) (.leaf (63)))) (.branch 62 (.branch 61 (.leaf (61)) (.leaf (56))) (.branch 63 (.leaf (49)) (.leaf (51))))))))
noncomputable def T (p : Fin 64) : Fin 64 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (16)) (.leaf (7))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (12)) (.leaf (2))) (.branch 7 (.leaf (13)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (22))) (.branch 11 (.leaf (5)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (9))) (.branch 15 (.leaf (25)) (.leaf (10)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (24)) (.leaf (11))) (.branch 19 (.leaf (14)) (.leaf (15)))) (.branch 22 (.branch 21 (.leaf (36)) (.leaf (17))) (.branch 23 (.leaf (32)) (.leaf (18))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (19)) (.leaf (20))) (.branch 27 (.leaf (39)) (.leaf (21)))) (.branch 30 (.branch 29 (.leaf (45)) (.leaf (23))) (.branch 31 (.leaf (26)) (.leaf (38))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (27)) (.leaf (28))) (.branch 35 (.leaf (53)) (.leaf (29)))) (.branch 38 (.branch 37 (.leaf (42)) (.leaf (30))) (.branch 39 (.leaf (31)) (.leaf (33))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (34)) (.leaf (47))) (.branch 43 (.leaf (35)) (.leaf (57)))) (.branch 46 (.branch 45 (.leaf (37)) (.leaf (50))) (.branch 47 (.leaf (40)) (.leaf (41)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (43)) (.leaf (62))) (.branch 51 (.leaf (44)) (.leaf (63)))) (.branch 54 (.branch 53 (.leaf (46)) (.leaf (48))) (.branch 55 (.leaf (49)) (.leaf (51))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (61)) (.leaf (52))) (.branch 59 (.leaf (54)) (.leaf (55)))) (.branch 62 (.branch 61 (.leaf (56)) (.leaf (60))) (.branch 63 (.leaf (58)) (.leaf (59))))))))
noncomputable def Ti (p : Fin 64) : Fin 64 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 64) : Fin 64 := T (S p)
theorem quotient_relations : (∀ p : Fin 64, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 128, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 128, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 64, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 64)) := [[0,3,11],[1,2,8],[4,5,13],[6,7,12],[9,10,18],[14,15,24],[16,17,25],[19],[20,21,30],[22,23,33],[26,27,38],[28,29,40],[31,32,39],[34,35,47],[36,37,48],[41,42,53],[43,44,54],[45,46,55],[49,50,59],[51,52,60],[56,57,58],[61,62,63]]
noncomputable def verticesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (12))) (.branch 11 (.leaf (13)) (.leaf (2)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (8))) (.branch 15 (.leaf (15)) (.leaf (16)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (18)) (.leaf (19))) (.branch 19 (.leaf (14)) (.leaf (21)))) (.branch 22 (.branch 21 (.leaf (22)) (.leaf (23))) (.branch 23 (.leaf (25)) (.leaf (26))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (17)) (.leaf (20))) (.branch 27 (.leaf (28)) (.leaf (29)))) (.branch 30 (.branch 29 (.leaf (31)) (.leaf (32))) (.branch 31 (.leaf (24)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (35)) (.leaf (27))) (.branch 35 (.leaf (37)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (40)) (.leaf (41))) (.branch 39 (.leaf (30)) (.leaf (36))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (33)) (.leaf (43))) (.branch 43 (.leaf (44)) (.leaf (46)))) (.branch 46 (.branch 45 (.leaf (47)) (.leaf (49))) (.branch 47 (.leaf (50)) (.leaf (39)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (42)) (.leaf (52))) (.branch 51 (.leaf (53)) (.leaf (55)))) (.branch 54 (.branch 53 (.leaf (56)) (.leaf (45))) (.branch 55 (.leaf (48)) (.leaf (51))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (58)) (.leaf (59))) (.branch 59 (.leaf (60)) (.leaf (54)))) (.branch 62 (.branch 61 (.leaf (57)) (.leaf (61))) (.branch 63 (.leaf (62)) (.leaf (63))))))))
noncomputable def verticesIndex (p : Fin 64) : Fin 64 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (11)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (13)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (9)) (.leaf (10))) (.branch 15 (.leaf (18)) (.leaf (14)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (15)) (.leaf (24))) (.branch 19 (.leaf (16)) (.leaf (17)))) (.branch 22 (.branch 21 (.leaf (25)) (.leaf (19))) (.branch 23 (.leaf (20)) (.leaf (21))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (30)) (.leaf (22))) (.branch 27 (.leaf (23)) (.leaf (33)))) (.branch 30 (.branch 29 (.leaf (26)) (.leaf (27))) (.branch 31 (.leaf (38)) (.leaf (28))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (29)) (.leaf (40))) (.branch 35 (.leaf (31)) (.leaf (32)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (34))) (.branch 39 (.leaf (35)) (.leaf (47))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (36)) (.leaf (37))) (.branch 43 (.leaf (48)) (.leaf (41)))) (.branch 46 (.branch 45 (.leaf (42)) (.leaf (53))) (.branch 47 (.leaf (43)) (.leaf (44)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (54)) (.leaf (45))) (.branch 51 (.leaf (46)) (.leaf (55)))) (.branch 54 (.branch 53 (.leaf (49)) (.leaf (50))) (.branch 55 (.leaf (59)) (.leaf (51))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (52)) (.leaf (60))) (.branch 59 (.leaf (56)) (.leaf (57)))) (.branch 62 (.branch 61 (.leaf (58)) (.leaf (61))) (.branch 63 (.leaf (62)) (.leaf (63))))))))
noncomputable def verticesBack (p : Fin 64) : Fin 64 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 64, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 64 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 64, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 64)) := [[0,1],[2,4],[3,6],[5,9],[7,8],[10,14],[11,16],[12,13],[15,19],[17,20],[18,22],[21,26],[23,28],[24,25],[27,31],[29,34],[30,36],[32,33],[35,41],[37,43],[38,39],[40,45],[42,48],[44,49],[46,51],[47,53],[50,55],[52,56],[54,57],[58,61],[59,62],[60,63]]
noncomputable def edgesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (8))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (9)) (.leaf (7))) (.branch 11 (.leaf (10)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (14)) (.leaf (15))) (.branch 15 (.leaf (11)) (.leaf (16)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (13)) (.leaf (18))) (.branch 19 (.leaf (20)) (.leaf (17)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (22))) (.branch 23 (.leaf (21)) (.leaf (24))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (26)) (.leaf (27))) (.branch 27 (.leaf (23)) (.leaf (28)))) (.branch 30 (.branch 29 (.leaf (25)) (.leaf (30))) (.branch 31 (.leaf (32)) (.leaf (29))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (34)) (.leaf (35))) (.branch 35 (.leaf (31)) (.leaf (36)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (38))) (.branch 39 (.leaf (40)) (.leaf (41))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (42)) (.leaf (37))) (.branch 43 (.leaf (44)) (.leaf (39)))) (.branch 46 (.branch 45 (.leaf (46)) (.leaf (43))) (.branch 47 (.leaf (48)) (.leaf (50)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (45)) (.leaf (47))) (.branch 51 (.leaf (52)) (.leaf (49)))) (.branch 54 (.branch 53 (.leaf (54)) (.leaf (51))) (.branch 55 (.leaf (56)) (.leaf (53))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (55)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (62)) (.leaf (59))) (.branch 63 (.leaf (61)) (.leaf (63))))))))
noncomputable def edgesIndex (p : Fin 64) : Fin 64 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (9))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (8))) (.branch 11 (.leaf (10)) (.leaf (14)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (16))) (.branch 15 (.leaf (12)) (.leaf (13)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (15)) (.leaf (19))) (.branch 19 (.leaf (17)) (.leaf (20)))) (.branch 22 (.branch 21 (.leaf (18)) (.leaf (22))) (.branch 23 (.leaf (21)) (.leaf (26))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (23)) (.leaf (28))) (.branch 27 (.leaf (24)) (.leaf (25)))) (.branch 30 (.branch 29 (.leaf (27)) (.leaf (31))) (.branch 31 (.leaf (29)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (30)) (.leaf (36))) (.branch 35 (.leaf (32)) (.leaf (33)))) (.branch 38 (.branch 37 (.leaf (35)) (.leaf (41))) (.branch 39 (.leaf (37)) (.leaf (43))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (38)) (.leaf (39))) (.branch 43 (.leaf (40)) (.leaf (45)))) (.branch 46 (.branch 45 (.leaf (42)) (.leaf (48))) (.branch 47 (.leaf (44)) (.leaf (49)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (46)) (.leaf (51))) (.branch 51 (.leaf (47)) (.leaf (53)))) (.branch 54 (.branch 53 (.leaf (50)) (.leaf (55))) (.branch 55 (.leaf (52)) (.leaf (56))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (54)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (61)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (62))) (.branch 63 (.leaf (60)) (.leaf (63))))))))
noncomputable def edgesBack (p : Fin 64) : Fin 64 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 64, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 64 := by decide +kernel
theorem edges_partition : ∀ p : Fin 64, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 64)) := [[0,2,5,10,15,19,24,16],[1,3,7],[4,8,12],[6,11,17,21,27,32,22,9,13],[14,18,23,29,35,42,36,20,25],[26,30,37,44,50,45,28,33,39],[31,38],[34,40,46,52,57,43,48,53],[41,47],[49,54,58,62],[51,55,59,63],[56,60,61]]
noncomputable def facesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (8))) (.branch 3 (.leaf (1)) (.leaf (9)))) (.branch 6 (.branch 5 (.leaf (11)) (.leaf (2))) (.branch 7 (.leaf (14)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (21))) (.branch 11 (.leaf (3)) (.leaf (15)))) (.branch 14 (.branch 13 (.leaf (13)) (.leaf (22))) (.branch 15 (.leaf (23)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (7)) (.leaf (16))) (.branch 19 (.leaf (24)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (30)) (.leaf (17))) (.branch 23 (.leaf (20)) (.leaf (25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (31))) (.branch 27 (.leaf (32)) (.leaf (18)))) (.branch 30 (.branch 29 (.leaf (38)) (.leaf (26))) (.branch 31 (.leaf (33)) (.leaf (41))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (19)) (.leaf (39))) (.branch 35 (.leaf (43)) (.leaf (27)))) (.branch 38 (.branch 37 (.leaf (29)) (.leaf (34))) (.branch 39 (.leaf (42)) (.leaf (40))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (44)) (.leaf (51))) (.branch 43 (.leaf (28)) (.leaf (48)))) (.branch 46 (.branch 45 (.leaf (35)) (.leaf (37))) (.branch 47 (.leaf (45)) (.leaf (52)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (49)) (.leaf (53))) (.branch 51 (.leaf (36)) (.leaf (57)))) (.branch 54 (.branch 53 (.leaf (46)) (.leaf (50))) (.branch 55 (.leaf (54)) (.leaf (58))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (61)) (.leaf (47))) (.branch 59 (.leaf (55)) (.leaf (59)))) (.branch 62 (.branch 61 (.leaf (62)) (.leaf (63))) (.branch 63 (.leaf (56)) (.leaf (60))))))))
noncomputable def facesIndex (p : Fin 64) : Fin 64 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (10)))) (.branch 6 (.branch 5 (.leaf (15)) (.leaf (19))) (.branch 7 (.leaf (24)) (.leaf (16))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (7)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (12))) (.branch 15 (.leaf (6)) (.leaf (11)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (17)) (.leaf (21))) (.branch 19 (.leaf (27)) (.leaf (32)))) (.branch 22 (.branch 21 (.leaf (22)) (.leaf (9))) (.branch 23 (.leaf (13)) (.leaf (14))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (18)) (.leaf (23))) (.branch 27 (.leaf (29)) (.leaf (35)))) (.branch 30 (.branch 29 (.leaf (42)) (.leaf (36))) (.branch 31 (.leaf (20)) (.leaf (25))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (26)) (.leaf (30))) (.branch 35 (.leaf (37)) (.leaf (44)))) (.branch 38 (.branch 37 (.leaf (50)) (.leaf (45))) (.branch 39 (.leaf (28)) (.leaf (33))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (39)) (.leaf (31))) (.branch 43 (.leaf (38)) (.leaf (34)))) (.branch 46 (.branch 45 (.leaf (40)) (.leaf (46))) (.branch 47 (.leaf (52)) (.leaf (57)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (43)) (.leaf (48))) (.branch 51 (.leaf (53)) (.leaf (41)))) (.branch 54 (.branch 53 (.leaf (47)) (.leaf (49))) (.branch 55 (.leaf (54)) (.leaf (58))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (62)) (.leaf (51))) (.branch 59 (.leaf (55)) (.leaf (59)))) (.branch 62 (.branch 61 (.leaf (63)) (.leaf (56))) (.branch 63 (.leaf (60)) (.leaf (61))))))))
noncomputable def facesBack (p : Fin 64) : Fin 64 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 64, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 64 := by decide +kernel
theorem faces_partition : ∀ p : Fin 64, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [8,3,3,9,9,9,2,8,2,4,4,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 22 - 32 + 12 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 1 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.leaf (⟨0,1,-1,-2⟩))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨2,-1,1,0⟩))) (.branch 11 (.leaf (⟨-1,-3,0,-1⟩)) (.leaf (⟨-1,-1,1,0⟩)))) (.branch 14 (.branch 13 (.leaf (⟨1,1,-2,-1⟩)) (.leaf (⟨2,1,1,1⟩))) (.branch 15 (.leaf (⟨-3,1,-1,0⟩)) (.leaf (⟨1,4,0,1⟩)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (⟨-1,1,0,-1⟩)) (.leaf (⟨1,2,-1,-1⟩))) (.branch 19 (.leaf (⟨-3,-2,-1,-1⟩)) (.leaf (⟨4,-1,1,0⟩)))) (.branch 22 (.branch 21 (.leaf (⟨2,-1,-1,1⟩)) (.leaf (⟨-1,-3,1,2⟩))) (.branch 23 (.leaf (⟨-2,3,-1,1⟩)) (.leaf (⟨3,5,1,2⟩))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (⟨4,3,1,1⟩)) (.leaf (⟨2,1,-1,0⟩))) (.branch 27 (.leaf (⟨-3,1,2,-1⟩)) (.leaf (⟨1,4,-1,-3⟩)))) (.branch 30 (.branch 29 (.leaf (⟨5,-3,2,-1⟩)) (.leaf (⟨-3,-8,-1,-3⟩))) (.branch 31 (.leaf (⟨-3,-2,2,1⟩)) (.leaf (⟨-7,-2,-3,-1⟩))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (⟨2,-5,1,-2⟩)) (.leaf (⟨5,2,2,1⟩))) (.branch 35 (.leaf (⟨-8,3,-3,1⟩)) (.leaf (⟨3,11,1,4⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-2,3,1,-2⟩)) (.leaf (⟨3,5,-2,-3⟩))) (.branch 39 (.leaf (⟨4,3,-3,-2⟩)) (.leaf (⟨-5,-7,-2,-3⟩))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (⟨-8,-5,-3,-2⟩)) (.leaf (⟨-7,-2,4,1⟩))) (.branch 43 (.leaf (⟨2,-5,-1,3⟩)) (.leaf (⟨5,-3,-3,2⟩)))) (.branch 46 (.branch 45 (.leaf (⟨-3,-8,2,5⟩)) (.leaf (⟨-5,8,-2,3⟩))) (.branch 47 (.leaf (⟨8,13,3,5⟩)) (.leaf (⟨11,8,4,3⟩)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (⟨5,2,-3,-1⟩)) (.leaf (⟨-18,-5,-7,-2⟩))) (.branch 51 (.leaf (⟨5,-13,2,-5⟩)) (.leaf (⟨13,-8,5,-3⟩)))) (.branch 54 (.branch 53 (.leaf (⟨-8,-21,-3,-8⟩)) (.leaf (⟨-5,-7,3,4⟩))) (.branch 55 (.leaf (⟨-8,-5,5,3⟩)) (.leaf (⟨13,5,5,2⟩))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (⟨13,5,-8,-3⟩)) (.leaf (⟨-5,8,3,-5⟩))) (.branch 59 (.leaf (⟨8,13,-5,-8⟩)) (.leaf (⟨-13,-18,-5,-7⟩)))) (.branch 62 (.branch 61 (.leaf (⟨-21,-13,-8,-5⟩)) (.leaf (⟨21,34,8,13⟩))) (.branch 63 (.leaf (⟨34,13,13,5⟩)) (.leaf (⟨-13,21,-5,8⟩))))))))
noncomputable def liftMatrix (p : Fin 64) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 64) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],13⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],14⟩,⟨⟨1,4,0,1⟩,[.t (4)],15⟩,⟨⟨-1,1,0,-1⟩,[.t (-1)],16⟩,⟨⟨1,2,-1,-1⟩,[.t (-1),.s,.t (1)],17⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],18⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],19⟩,⟨⟨2,-1,-1,1⟩,[.t (-2),.s,.t (-1)],20⟩,⟨⟨-1,-3,1,2⟩,[.t (-1),.s,.t (2)],21⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],22⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],23⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],24⟩,⟨⟨2,1,-1,0⟩,[.t (-2),.s,.t (0)],25⟩,⟨⟨-3,1,2,-1⟩,[.t (-2),.s,.t (-2),.s,.t (-1)],26⟩,⟨⟨1,4,-1,-3⟩,[.t (-1),.s,.t (3)],27⟩,⟨⟨5,-3,2,-1⟩,[.t (2),.s,.t (-2),.s,.t (-1)],28⟩,⟨⟨-3,-8,-1,-3⟩,[.t (3),.s,.t (3)],29⟩,⟨⟨-3,-2,2,1⟩,[.t (-2),.s,.t (-2),.s,.t (0)],30⟩,⟨⟨-7,-2,-3,-1⟩,[.t (2),.s,.t (-3),.s,.t (0)],31⟩,⟨⟨2,-5,1,-2⟩,[.t (2),.s,.t (-2)],32⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],33⟩,⟨⟨-8,3,-3,1⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],34⟩,⟨⟨3,11,1,4⟩,[.t (3),.s,.t (4)],35⟩,⟨⟨-2,3,1,-2⟩,[.t (-2),.s,.t (-2)],36⟩,⟨⟨3,5,-2,-3⟩,[.t (-2),.s,.t (-2),.s,.t (1)],37⟩,⟨⟨4,3,-3,-2⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],38⟩,⟨⟨-5,-7,-2,-3⟩,[.t (2),.s,.t (-2),.s,.t (1)],39⟩,⟨⟨-8,-5,-3,-2⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (0)],40⟩,⟨⟨-7,-2,4,1⟩,[.t (-2),.s,.t (-4),.s,.t (0)],41⟩,⟨⟨2,-5,-1,3⟩,[.t (-2),.s,.t (-3)],42⟩,⟨⟨5,-3,-3,2⟩,[.t (-2),.s,.t (-3),.s,.t (-1)],43⟩,⟨⟨-3,-8,2,5⟩,[.t (-2),.s,.t (-2),.s,.t (2)],44⟩,⟨⟨-5,8,-2,3⟩,[.t (2),.s,.t (-2),.s,.t (-2)],45⟩,⟨⟨8,13,3,5⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (1)],46⟩,⟨⟨11,8,4,3⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],47⟩,⟨⟨5,2,-3,-1⟩,[.t (-2),.s,.t (-3),.s,.t (0)],48⟩,⟨⟨-18,-5,-7,-2⟩,[.t (2),.s,.t (-2),.s,.t (-4),.s,.t (0)],49⟩,⟨⟨5,-13,2,-5⟩,[.t (2),.s,.t (-2),.s,.t (-3)],50⟩,⟨⟨13,-8,5,-3⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-1)],51⟩,⟨⟨-8,-21,-3,-8⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (2)],52⟩,⟨⟨-5,-7,3,4⟩,[.t (-2),.s,.t (-3),.s,.t (1)],53⟩,⟨⟨-8,-5,5,3⟩,[.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],54⟩,⟨⟨13,5,5,2⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (0)],55⟩,⟨⟨13,5,-8,-3⟩,[.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (0)],56⟩,⟨⟨-5,8,3,-5⟩,[.t (-2),.s,.t (-3),.s,.t (-2)],57⟩,⟨⟨8,13,-5,-8⟩,[.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (1)],58⟩,⟨⟨-13,-18,-5,-7⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (1)],59⟩,⟨⟨-21,-13,-8,-5⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],60⟩,⟨⟨21,34,8,13⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (1)],61⟩,⟨⟨34,13,13,5⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (0)],62⟩,⟨⟨-13,21,-5,8⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],63⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 64 ∧ ((List.finRange 64).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 64) := [⟨25,3,⟨⟨4,11,1,3⟩,[.t (4),.s,.t (3)],0⟩⟩,⟨41,5,⟨⟨-23,-43,-8,-15⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨53,8,⟨⟨-65,-111,-24,-41⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨56,9,⟨⟨-127,-209,-48,-79⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨58,10,⟨⟨-377,-610,-144,-233⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨44,7,⟨⟨-61,-94,-24,-37⟩,[.t (2),.s,.t (-2),.s,.t (-7),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨38,6,⟨⟨29,41,12,17⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (1)],0⟩⟩,⟨27,4,⟨⟨13,15,6,7⟩,[.t (2),.s,.t (-6),.s,.t (1)],0⟩⟩,⟨12,2,⟨⟨-5,-3,-3,-2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,1,⟨⟨1,0,3,1⟩,[.t (0),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨8,1,⟨⟨1,0,-3,1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨13,2,⟨⟨-2,3,3,-5⟩,[.t (-1),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨31,4,⟨⟨7,-15,-6,13⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨39,6,⟨⟨17,-41,-12,29⟩,[.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨49,7,⟨⟨-37,94,24,-61⟩,[.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨59,11,⟨⟨-261,676,-100,259⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-5),.s,.t (-2),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨62,11,⟨⟨259,-676,100,-261⟩,[.t (2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨61,10,⟨⟨-233,610,144,-377⟩,[.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-3),.s,.t (-3),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨52,9,⟨⟨-79,209,48,-127⟩,[.t (-2),.s,.t (-3),.s,.t (-6),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨47,8,⟨⟨-41,111,24,-65⟩,[.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨35,5,⟨⟨-15,43,8,-23⟩,[.t (-2),.s,.t (-8),.s,.t (-3)],0⟩⟩,⟨24,3,⟨⟨3,-11,-1,4⟩,[.t (-3),.s,.t (-4)],0⟩⟩,⟨19,-3,⟨⟨5,-21,1,-4⟩,[.t (5),.s,.t (-4)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-2,1),(-7,4),(-5,3),(-13,8),(-8,5),(-3,2),(-4,3),(-1,1),(-1,2),(0,1),(1,1),(2,1),(7,3),(5,2),(18,7),(13,5),(34,13),(21,8),(8,3),(11,4),(3,1),(4,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end PSL2_17_c10

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
