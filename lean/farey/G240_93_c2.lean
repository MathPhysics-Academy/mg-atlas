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
namespace G240_93_c2
noncomputable def originalSData : LookupTree (Fin 120) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (8))) (.branch 6 (.leaf (7)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (12)) (.leaf (11))) (.branch 10 (.leaf (13)) (.leaf (9)))) (.branch 13 (.branch 12 (.leaf (15)) (.leaf (2))) (.branch 14 (.leaf (16)) (.leaf (18)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (10)) (.leaf (20)))) (.branch 20 (.branch 19 (.leaf (17)) (.leaf (22))) (.branch 21 (.leaf (14)) (.leaf (24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (21)) (.leaf (27))) (.branch 25 (.leaf (19)) (.leaf (30)))) (.branch 28 (.branch 27 (.leaf (32)) (.leaf (25))) (.branch 29 (.leaf (35)) (.leaf (37))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (23)) (.branch 32 (.leaf (40)) (.leaf (29)))) (.branch 35 (.branch 34 (.leaf (42)) (.leaf (44))) (.branch 36 (.leaf (31)) (.leaf (47))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (26)) (.leaf (49))) (.branch 40 (.leaf (51)) (.leaf (28)))) (.branch 43 (.branch 42 (.leaf (54)) (.leaf (38))) (.branch 44 (.leaf (57)) (.leaf (39)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (58)) (.branch 47 (.leaf (59)) (.leaf (41)))) (.branch 50 (.branch 49 (.leaf (60)) (.leaf (33))) (.branch 51 (.leaf (63)) (.leaf (34))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (64)) (.leaf (65))) (.branch 55 (.leaf (36)) (.leaf (66)))) (.branch 58 (.branch 57 (.leaf (68)) (.leaf (50))) (.branch 59 (.leaf (52)) (.leaf (53)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (55)) (.branch 62 (.leaf (71)) (.leaf (73)))) (.branch 65 (.branch 64 (.leaf (43)) (.leaf (45))) (.branch 66 (.leaf (46)) (.leaf (48))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (76)) (.leaf (62))) (.branch 70 (.leaf (78)) (.leaf (80)))) (.branch 73 (.branch 72 (.leaf (67)) (.leaf (83))) (.branch 74 (.leaf (56)) (.leaf (85)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (87)) (.branch 77 (.leaf (61)) (.leaf (90)))) (.branch 80 (.branch 79 (.leaf (74)) (.leaf (93))) (.branch 81 (.leaf (75)) (.leaf (95))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (97)) (.leaf (77))) (.branch 85 (.leaf (99)) (.leaf (69)))) (.branch 88 (.branch 87 (.leaf (102)) (.leaf (70))) (.branch 89 (.leaf (104)) (.leaf (106))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (72)) (.branch 92 (.leaf (108)) (.leaf (110)))) (.branch 95 (.branch 94 (.leaf (86)) (.leaf (105))) (.branch 96 (.leaf (88)) (.leaf (94))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (89)) (.leaf (109))) (.branch 100 (.leaf (91)) (.leaf (98)))) (.branch 103 (.branch 102 (.leaf (115)) (.leaf (79))) (.branch 104 (.leaf (96)) (.leaf (81)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (103)) (.branch 107 (.leaf (82)) (.leaf (100)))) (.branch 110 (.branch 109 (.leaf (84)) (.leaf (107))) (.branch 111 (.leaf (101)) (.leaf (112))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (116)) (.leaf (114))) (.branch 115 (.leaf (118)) (.leaf (92)))) (.branch 118 (.branch 117 (.leaf (117)) (.leaf (111))) (.branch 119 (.leaf (119)) (.leaf (113)))))))))
noncomputable def originalS (p : Fin 120) : Fin 120 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 120) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (9))) (.branch 6 (.leaf (10)) (.leaf (11))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (5))) (.branch 10 (.leaf (1)) (.leaf (14)))) (.branch 13 (.branch 12 (.leaf (16)) (.leaf (13))) (.branch 14 (.leaf (17)) (.leaf (19)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (12)) (.branch 17 (.leaf (6)) (.leaf (21)))) (.branch 20 (.branch 19 (.leaf (15)) (.leaf (23))) (.branch 21 (.leaf (8)) (.leaf (25))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (26)) (.leaf (28))) (.branch 25 (.leaf (29)) (.leaf (31)))) (.branch 28 (.branch 27 (.leaf (33)) (.leaf (34))) (.branch 29 (.leaf (36)) (.leaf (38))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (39)) (.branch 32 (.leaf (41)) (.leaf (18)))) (.branch 35 (.branch 34 (.leaf (43)) (.leaf (45))) (.branch 36 (.leaf (46)) (.leaf (48))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (20)) (.leaf (50))) (.branch 40 (.leaf (52)) (.leaf (53)))) (.branch 43 (.branch 42 (.leaf (55)) (.leaf (56))) (.branch 44 (.leaf (51)) (.leaf (22)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (49)) (.branch 47 (.leaf (40)) (.leaf (59)))) (.branch 50 (.branch 49 (.leaf (61)) (.leaf (62))) (.branch 51 (.leaf (44)) (.leaf (24))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (42)) (.leaf (35))) (.branch 55 (.leaf (65)) (.leaf (67)))) (.branch 58 (.branch 57 (.leaf (69)) (.leaf (58))) (.branch 59 (.leaf (57)) (.leaf (27)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (70)) (.branch 62 (.leaf (72)) (.leaf (74)))) (.branch 65 (.branch 64 (.leaf (64)) (.leaf (63))) (.branch 66 (.leaf (30)) (.leaf (75))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (77)) (.leaf (32))) (.branch 70 (.leaf (79)) (.leaf (81)))) (.branch 73 (.branch 72 (.leaf (82)) (.leaf (84))) (.branch 74 (.leaf (37)) (.leaf (86)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (88)) (.branch 77 (.leaf (89)) (.leaf (91)))) (.branch 80 (.branch 79 (.leaf (92)) (.leaf (94))) (.branch 81 (.leaf (47)) (.leaf (96))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (93)) (.leaf (98))) (.branch 85 (.leaf (100)) (.leaf (101)))) (.branch 88 (.branch 87 (.leaf (103)) (.leaf (54))) (.branch 89 (.leaf (105)) (.leaf (102))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (107)) (.branch 92 (.leaf (109)) (.leaf (85)))) (.branch 95 (.branch 94 (.leaf (110)) (.leaf (111))) (.branch 96 (.leaf (112)) (.leaf (97))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (60)) (.leaf (113))) (.branch 100 (.leaf (114)) (.leaf (76)))) (.branch 103 (.branch 102 (.leaf (78)) (.leaf (115))) (.branch 104 (.leaf (116)) (.leaf (117)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (106)) (.branch 107 (.leaf (66)) (.leaf (118)))) (.branch 110 (.branch 109 (.leaf (119)) (.leaf (71))) (.branch 111 (.leaf (68)) (.leaf (87))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (95)) (.leaf (90))) (.branch 115 (.leaf (99)) (.leaf (73)))) (.branch 118 (.branch 117 (.leaf (80)) (.leaf (104))) (.branch 119 (.leaf (83)) (.leaf (108)))))))))
noncomputable def originalT (p : Fin 120) : Fin 120 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 60) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (2)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (3)) (.leaf (4))) (.branch 14 (.leaf (7)) (.leaf (8)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (6)) (.leaf (8)))) (.branch 20 (.branch 19 (.leaf (9)) (.leaf (10))) (.branch 21 (.leaf (9)) (.leaf (10))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (11)) (.leaf (12))) (.branch 25 (.leaf (11)) (.leaf (12)))) (.branch 28 (.branch 27 (.leaf (13)) (.leaf (14))) (.branch 29 (.leaf (15)) (.leaf (13))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16)))) (.branch 35 (.branch 34 (.leaf (17)) (.leaf (18))) (.branch 36 (.leaf (19)) (.leaf (20))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (16)) (.leaf (17))) (.branch 40 (.leaf (18)) (.leaf (19)))) (.branch 43 (.branch 42 (.leaf (20)) (.leaf (21))) (.branch 44 (.leaf (22)) (.leaf (23)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (24)) (.branch 47 (.leaf (25)) (.leaf (26)))) (.branch 50 (.branch 49 (.leaf (27)) (.leaf (21))) (.branch 51 (.leaf (22)) (.leaf (23))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (24)) (.leaf (25))) (.branch 55 (.leaf (26)) (.leaf (27)))) (.branch 58 (.branch 57 (.leaf (28)) (.leaf (29))) (.branch 59 (.leaf (30)) (.leaf (31)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (32)) (.branch 62 (.leaf (33)) (.leaf (28)))) (.branch 65 (.branch 64 (.leaf (29)) (.leaf (30))) (.branch 66 (.leaf (31)) (.leaf (32))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (33)) (.leaf (34))) (.branch 70 (.leaf (35)) (.leaf (36)))) (.branch 73 (.branch 72 (.leaf (37)) (.leaf (38))) (.branch 74 (.leaf (34)) (.leaf (35)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (36)) (.branch 77 (.leaf (37)) (.leaf (38)))) (.branch 80 (.branch 79 (.leaf (39)) (.leaf (40))) (.branch 81 (.leaf (41)) (.leaf (42))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (43)) (.leaf (44))) (.branch 85 (.leaf (45)) (.leaf (39)))) (.branch 88 (.branch 87 (.leaf (40)) (.leaf (41))) (.branch 89 (.leaf (42)) (.leaf (43))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (44)) (.branch 92 (.leaf (45)) (.leaf (46)))) (.branch 95 (.branch 94 (.leaf (47)) (.leaf (48))) (.branch 96 (.leaf (49)) (.leaf (50))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (51)) (.leaf (52))) (.branch 100 (.leaf (53)) (.leaf (54)))) (.branch 103 (.branch 102 (.leaf (46)) (.leaf (47))) (.branch 104 (.leaf (48)) (.leaf (49)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (50)) (.branch 107 (.leaf (51)) (.leaf (52)))) (.branch 110 (.branch 109 (.leaf (53)) (.leaf (54))) (.branch 111 (.leaf (55)) (.leaf (56))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (57)) (.leaf (58))) (.branch 115 (.leaf (59)) (.leaf (55)))) (.branch 118 (.branch 117 (.leaf (56)) (.leaf (57))) (.branch 119 (.leaf (58)) (.leaf (59)))))))))
noncomputable def projection (p : Fin 120) : Fin 60 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 120) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (5))) (.branch 6 (.leaf (8)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (10)) (.leaf (14))) (.branch 10 (.leaf (18)) (.leaf (19)))) (.branch 13 (.branch 12 (.leaf (22)) (.leaf (23))) (.branch 14 (.leaf (26)) (.leaf (27)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (28)) (.branch 17 (.leaf (32)) (.leaf (33)))) (.branch 20 (.branch 19 (.leaf (34)) (.leaf (35))) (.branch 21 (.leaf (36)) (.leaf (42))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (43)) (.leaf (44))) (.branch 25 (.leaf (45)) (.leaf (46)))) (.branch 28 (.branch 27 (.leaf (47)) (.leaf (48))) (.branch 29 (.leaf (56)) (.leaf (57))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (58)) (.branch 32 (.leaf (59)) (.leaf (60)))) (.branch 35 (.branch 34 (.leaf (61)) (.leaf (68))) (.branch 36 (.leaf (69)) (.leaf (70))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (71)) (.leaf (72))) (.branch 40 (.leaf (78)) (.leaf (79)))) (.branch 43 (.branch 42 (.leaf (80)) (.leaf (81))) (.branch 44 (.leaf (82)) (.leaf (83)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (84)) (.branch 47 (.leaf (92)) (.leaf (93)))) (.branch 50 (.branch 49 (.leaf (94)) (.leaf (95))) (.branch 51 (.leaf (96)) (.leaf (97))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (98)) (.leaf (99))) (.branch 55 (.leaf (100)) (.leaf (110)))) (.branch 58 (.branch 57 (.leaf (111)) (.leaf (112))) (.branch 59 (.leaf (113)) (.leaf (114))))))))
noncomputable def representative (p : Fin 60) : Fin 120 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (5)) (.leaf (2))) (.branch 6 (.leaf (3)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (9))) (.branch 10 (.leaf (8)) (.leaf (11)))) (.branch 13 (.branch 12 (.leaf (10)) (.leaf (14))) (.branch 14 (.leaf (16)) (.leaf (12)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (19)) (.branch 17 (.leaf (13)) (.leaf (21)))) (.branch 20 (.branch 19 (.leaf (23)) (.leaf (15))) (.branch 21 (.leaf (26)) (.leaf (17))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (29)) (.leaf (18))) (.branch 25 (.leaf (30)) (.leaf (31)))) (.branch 28 (.branch 27 (.leaf (20)) (.leaf (32))) (.branch 29 (.leaf (34)) (.leaf (22))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (24)) (.branch 32 (.leaf (25)) (.leaf (27)))) (.branch 35 (.branch 34 (.leaf (37)) (.leaf (28))) (.branch 36 (.leaf (39)) (.leaf (41))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (33)) (.leaf (44))) (.branch 40 (.leaf (35)) (.leaf (47)))) (.branch 43 (.branch 42 (.leaf (36)) (.leaf (49))) (.branch 44 (.leaf (51)) (.leaf (38)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (53)) (.branch 47 (.leaf (55)) (.leaf (40)))) (.branch 50 (.branch 49 (.leaf (50)) (.leaf (42))) (.branch 51 (.leaf (48)) (.leaf (43))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (54)) (.leaf (45))) (.branch 55 (.leaf (52)) (.leaf (46)))) (.branch 58 (.branch 57 (.leaf (57)) (.leaf (56))) (.branch 59 (.leaf (59)) (.leaf (58))))))))
noncomputable def S (p : Fin 60) : Fin 60 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (7))) (.branch 6 (.leaf (4)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (10))) (.branch 10 (.leaf (5)) (.leaf (12)))) (.branch 13 (.branch 12 (.leaf (13)) (.leaf (15))) (.branch 14 (.leaf (17)) (.leaf (18)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (20)) (.branch 17 (.leaf (9)) (.leaf (22)))) (.branch 20 (.branch 19 (.leaf (24)) (.leaf (25))) (.branch 21 (.leaf (27)) (.leaf (28))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (23)) (.leaf (11))) (.branch 25 (.leaf (21)) (.leaf (19)))) (.branch 28 (.branch 27 (.leaf (31)) (.leaf (33))) (.branch 29 (.leaf (35)) (.leaf (30))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (29)) (.branch 32 (.leaf (14)) (.leaf (36)))) (.branch 35 (.branch 34 (.leaf (38)) (.leaf (16))) (.branch 36 (.leaf (40)) (.leaf (42))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (43)) (.leaf (45))) (.branch 40 (.leaf (46)) (.leaf (48)))) (.branch 43 (.branch 42 (.leaf (26)) (.leaf (50))) (.branch 44 (.leaf (47)) (.leaf (52)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (54)) (.branch 47 (.leaf (39)) (.leaf (55)))) (.branch 50 (.branch 49 (.leaf (56)) (.leaf (57))) (.branch 51 (.leaf (51)) (.leaf (32))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (58)) (.leaf (59))) (.branch 55 (.leaf (37)) (.leaf (34)))) (.branch 58 (.branch 57 (.leaf (41)) (.leaf (49))) (.branch 59 (.leaf (44)) (.leaf (53))))))))
noncomputable def T (p : Fin 60) : Fin 60 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (6)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (5))) (.branch 6 (.leaf (9)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (7))) (.branch 10 (.leaf (16)) (.leaf (8)))) (.branch 13 (.branch 12 (.leaf (23)) (.leaf (10))) (.branch 14 (.leaf (11)) (.leaf (31)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (12)) (.branch 17 (.leaf (34)) (.leaf (13)))) (.branch 20 (.branch 19 (.leaf (14)) (.leaf (25))) (.branch 21 (.leaf (15)) (.leaf (24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (17)) (.leaf (22))) (.branch 25 (.leaf (18)) (.leaf (19)))) (.branch 28 (.branch 27 (.leaf (41)) (.leaf (20))) (.branch 29 (.leaf (21)) (.leaf (30))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (29)) (.branch 32 (.leaf (26)) (.leaf (51)))) (.branch 35 (.branch 34 (.leaf (27)) (.leaf (55))) (.branch 36 (.leaf (28)) (.leaf (32))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (54)) (.leaf (33))) (.branch 40 (.leaf (46)) (.leaf (35)))) (.branch 43 (.branch 42 (.leaf (56)) (.leaf (36))) (.branch 44 (.leaf (37)) (.leaf (58)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (38)) (.branch 47 (.leaf (39)) (.leaf (43)))) (.branch 50 (.branch 49 (.leaf (40)) (.leaf (57))) (.branch 51 (.leaf (42)) (.leaf (50))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (44)) (.leaf (59))) (.branch 55 (.leaf (45)) (.leaf (47)))) (.branch 58 (.branch 57 (.leaf (48)) (.leaf (49))) (.branch 59 (.leaf (52)) (.leaf (53))))))))
noncomputable def Ti (p : Fin 60) : Fin 60 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 60) : Fin 60 := T (S p)
theorem quotient_relations : (∀ p : Fin 60, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 120, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 120, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 60, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 60)) := [[0,3,4],[1,2,7],[5,6,8],[9,10,13],[11,12,18],[14,15,25],[16,17,28],[19,20,31],[21,22,30],[23,24,29],[26,27,36],[32,33,43],[34,35,46],[37,38,52],[39,40,55],[41,42,57],[44,45,59],[47,48,51],[49,50,56],[53,54,58]]
noncomputable def verticesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (6)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (8))) (.branch 10 (.leaf (9)) (.leaf (10)))) (.branch 13 (.branch 12 (.leaf (12)) (.leaf (13))) (.branch 14 (.leaf (11)) (.leaf (15)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (16)) (.branch 17 (.leaf (18)) (.leaf (19)))) (.branch 20 (.branch 19 (.leaf (14)) (.leaf (21))) (.branch 21 (.leaf (22)) (.leaf (24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (25)) (.leaf (27))) (.branch 25 (.leaf (28)) (.leaf (17)))) (.branch 28 (.branch 27 (.leaf (30)) (.leaf (31))) (.branch 29 (.leaf (20)) (.leaf (29))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (26)) (.branch 32 (.leaf (23)) (.leaf (33)))) (.branch 35 (.branch 34 (.leaf (34)) (.leaf (36))) (.branch 36 (.leaf (37)) (.leaf (32))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (39)) (.leaf (40))) (.branch 40 (.leaf (42)) (.leaf (43)))) (.branch 43 (.branch 42 (.leaf (45)) (.leaf (46))) (.branch 44 (.leaf (35)) (.leaf (48)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (49)) (.branch 47 (.leaf (38)) (.leaf (51)))) (.branch 50 (.branch 49 (.leaf (52)) (.leaf (54))) (.branch 51 (.leaf (55)) (.leaf (53))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (41)) (.leaf (57))) (.branch 55 (.leaf (58)) (.leaf (44)))) (.branch 58 (.branch 57 (.leaf (56)) (.leaf (47))) (.branch 59 (.leaf (59)) (.leaf (50))))))))
noncomputable def verticesIndex (p : Fin 60) : Fin 60 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (7)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (8))) (.branch 10 (.leaf (9)) (.leaf (10)))) (.branch 13 (.branch 12 (.leaf (13)) (.leaf (11))) (.branch 14 (.leaf (12)) (.leaf (18)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (14)) (.branch 17 (.leaf (15)) (.leaf (25)))) (.branch 20 (.branch 19 (.leaf (16)) (.leaf (17))) (.branch 21 (.leaf (28)) (.leaf (19))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (20)) (.leaf (31))) (.branch 25 (.leaf (21)) (.leaf (22)))) (.branch 28 (.branch 27 (.leaf (30)) (.leaf (23))) (.branch 29 (.leaf (24)) (.leaf (29))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (26)) (.branch 32 (.leaf (27)) (.leaf (36)))) (.branch 35 (.branch 34 (.leaf (32)) (.leaf (33))) (.branch 36 (.leaf (43)) (.leaf (34))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (35)) (.leaf (46))) (.branch 40 (.leaf (37)) (.leaf (38)))) (.branch 43 (.branch 42 (.leaf (52)) (.leaf (39))) (.branch 44 (.leaf (40)) (.leaf (55)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (41)) (.branch 47 (.leaf (42)) (.leaf (57)))) (.branch 50 (.branch 49 (.leaf (44)) (.leaf (45))) (.branch 51 (.leaf (59)) (.leaf (47))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (48)) (.leaf (51))) (.branch 55 (.leaf (49)) (.leaf (50)))) (.branch 58 (.branch 57 (.leaf (56)) (.leaf (53))) (.branch 59 (.leaf (54)) (.leaf (58))))))))
noncomputable def verticesBack (p : Fin 60) : Fin 60 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 60, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 60 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 60, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 60)) := [[0,1],[2,4],[3,5],[6,7],[8,9],[10,11],[12,14],[13,16],[15,19],[17,21],[18,23],[20,26],[22,29],[24,30],[25,31],[27,32],[28,34],[33,37],[35,39],[36,41],[38,44],[40,47],[42,49],[43,51],[45,53],[46,55],[48,50],[52,54],[56,57],[58,59]]
noncomputable def edgesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (8))) (.branch 10 (.leaf (9)) (.leaf (10)))) (.branch 13 (.branch 12 (.leaf (11)) (.leaf (12))) (.branch 14 (.leaf (14)) (.leaf (13)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (16)) (.branch 17 (.leaf (15)) (.leaf (18)))) (.branch 20 (.branch 19 (.leaf (20)) (.leaf (17))) (.branch 21 (.leaf (22)) (.leaf (19))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (24)) (.leaf (21))) (.branch 25 (.leaf (26)) (.leaf (28)))) (.branch 28 (.branch 27 (.leaf (23)) (.leaf (30))) (.branch 29 (.leaf (32)) (.leaf (25))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (29)) (.leaf (31)))) (.branch 35 (.branch 34 (.leaf (34)) (.leaf (33))) (.branch 36 (.leaf (36)) (.leaf (38))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (35)) (.leaf (40))) (.branch 40 (.leaf (37)) (.leaf (42)))) (.branch 43 (.branch 42 (.leaf (39)) (.leaf (44))) (.branch 44 (.leaf (46)) (.leaf (41)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (48)) (.branch 47 (.leaf (50)) (.leaf (43)))) (.branch 50 (.branch 49 (.leaf (52)) (.leaf (45))) (.branch 51 (.leaf (53)) (.leaf (47))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (54)) (.leaf (49))) (.branch 55 (.leaf (55)) (.leaf (51)))) (.branch 58 (.branch 57 (.leaf (56)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (59))))))))
noncomputable def edgesIndex (p : Fin 60) : Fin 60 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (5)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (8))) (.branch 10 (.leaf (9)) (.leaf (10)))) (.branch 13 (.branch 12 (.leaf (11)) (.leaf (12))) (.branch 14 (.leaf (14)) (.leaf (13)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (16)) (.branch 17 (.leaf (15)) (.leaf (19)))) (.branch 20 (.branch 19 (.leaf (17)) (.leaf (21))) (.branch 21 (.leaf (18)) (.leaf (23))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (20)) (.leaf (26))) (.branch 25 (.leaf (22)) (.leaf (29)))) (.branch 28 (.branch 27 (.leaf (24)) (.leaf (30))) (.branch 29 (.leaf (25)) (.leaf (31))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (32)) (.leaf (28)))) (.branch 35 (.branch 34 (.leaf (34)) (.leaf (33))) (.branch 36 (.leaf (37)) (.leaf (35))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (39)) (.leaf (36))) (.branch 40 (.leaf (41)) (.leaf (38)))) (.branch 43 (.branch 42 (.leaf (44)) (.leaf (40))) (.branch 44 (.leaf (47)) (.leaf (42)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (49)) (.branch 47 (.leaf (43)) (.leaf (51)))) (.branch 50 (.branch 49 (.leaf (45)) (.leaf (53))) (.branch 51 (.leaf (46)) (.leaf (55))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (48)) (.leaf (50))) (.branch 55 (.leaf (52)) (.leaf (54)))) (.branch 58 (.branch 57 (.leaf (56)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (59))))))))
noncomputable def edgesBack (p : Fin 60) : Fin 60 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 60, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 60 := by decide +kernel
theorem edges_partition : ∀ p : Fin 60, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 60)) := [[0,2],[1,3,6],[4,7,8,10,12,15,20,27,33,38,45,54,37,43,47,55,34,16,9,5],[11,13,17,22,23],[14,18,24,21,28,35,40,48,56,41,26,31],[19,25],[29,30],[32,36,42,50,51],[39,46],[44,52,58],[49,57],[53,59]]
noncomputable def facesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (5))) (.branch 6 (.leaf (24)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (6)) (.leaf (7))) (.branch 10 (.leaf (23)) (.leaf (8)))) (.branch 13 (.branch 12 (.leaf (25)) (.leaf (9))) (.branch 14 (.leaf (26)) (.leaf (30)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (10)) (.branch 17 (.leaf (22)) (.leaf (27)))) (.branch 20 (.branch 19 (.leaf (31)) (.leaf (42))) (.branch 21 (.leaf (11)) (.leaf (33))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (28)) (.leaf (29))) (.branch 25 (.leaf (32)) (.leaf (43)))) (.branch 28 (.branch 27 (.leaf (40)) (.leaf (12))) (.branch 29 (.leaf (34)) (.leaf (44))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (45)) (.branch 32 (.leaf (41)) (.leaf (46)))) (.branch 35 (.branch 34 (.leaf (13)) (.leaf (21))) (.branch 36 (.leaf (35)) (.leaf (47))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (17)) (.leaf (14))) (.branch 40 (.leaf (51)) (.leaf (36)))) (.branch 43 (.branch 42 (.leaf (39)) (.leaf (48))) (.branch 44 (.leaf (18)) (.leaf (53)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (15)) (.branch 47 (.leaf (52)) (.leaf (19)))) (.branch 50 (.branch 49 (.leaf (37)) (.leaf (56))) (.branch 51 (.leaf (49)) (.leaf (50))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (54)) (.leaf (58))) (.branch 55 (.leaf (16)) (.leaf (20)))) (.branch 58 (.branch 57 (.leaf (38)) (.leaf (57))) (.branch 59 (.leaf (55)) (.leaf (59))))))))
noncomputable def facesIndex (p : Fin 60) : Fin 60 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (6))) (.branch 6 (.leaf (4)) (.leaf (7))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (10))) (.branch 10 (.leaf (12)) (.leaf (15)))) (.branch 13 (.branch 12 (.leaf (20)) (.leaf (27))) (.branch 14 (.leaf (33)) (.leaf (38)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (45)) (.branch 17 (.leaf (54)) (.leaf (37)))) (.branch 20 (.branch 19 (.leaf (43)) (.leaf (47))) (.branch 21 (.leaf (55)) (.leaf (34))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (16)) (.leaf (9))) (.branch 25 (.leaf (5)) (.leaf (11)))) (.branch 28 (.branch 27 (.leaf (13)) (.leaf (17))) (.branch 29 (.leaf (22)) (.leaf (23))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (14)) (.branch 32 (.leaf (18)) (.leaf (24)))) (.branch 35 (.branch 34 (.leaf (21)) (.leaf (28))) (.branch 36 (.leaf (35)) (.leaf (40))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (48)) (.leaf (56))) (.branch 40 (.leaf (41)) (.leaf (26)))) (.branch 43 (.branch 42 (.leaf (31)) (.leaf (19))) (.branch 44 (.leaf (25)) (.leaf (29)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (30)) (.branch 47 (.leaf (32)) (.leaf (36)))) (.branch 50 (.branch 49 (.leaf (42)) (.leaf (50))) (.branch 51 (.leaf (51)) (.leaf (39))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (46)) (.leaf (44))) (.branch 55 (.leaf (52)) (.leaf (58)))) (.branch 58 (.branch 57 (.leaf (49)) (.leaf (57))) (.branch 59 (.leaf (53)) (.leaf (59))))))))
noncomputable def facesBack (p : Fin 60) : Fin 60 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 60, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 60 := by decide +kernel
theorem faces_partition : ∀ p : Fin 60, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [2,3,20,5,12,2,2,5,2,3,2,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 20 - 30 + 12 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 5 (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 6 (.leaf (⟨-1,0,1,-1⟩)) (.leaf (⟨0,1,-1,-2⟩))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨1,1,-2,-1⟩))) (.branch 10 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-2,2,3⟩)))) (.branch 13 (.branch 12 (.leaf (⟨-2,1,3,-2⟩)) (.leaf (⟨1,3,-2,-5⟩))) (.branch 14 (.leaf (⟨-2,-1,3,1⟩)) (.leaf (⟨3,-1,-5,2⟩)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (⟨-1,-4,2,7⟩)) (.branch 17 (.leaf (⟨-1,2,1,-3⟩)) (.leaf (⟨2,3,-3,-4⟩)))) (.branch 20 (.branch 19 (.leaf (⟨3,2,-5,-3⟩)) (.leaf (⟨-4,1,7,-2⟩))) (.branch 21 (.leaf (⟨1,5,-2,-9⟩)) (.leaf (⟨3,-2,-4,3⟩))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (⟨-2,-5,3,7⟩)) (.leaf (⟨2,-3,-3,5⟩))) (.branch 25 (.leaf (⟨-3,-5,5,8⟩)) (.leaf (⟨-4,-3,7,5⟩)))) (.branch 28 (.branch 27 (.leaf (⟨5,-1,-9,2⟩)) (.leaf (⟨-1,-6,2,11⟩))) (.branch 29 (.leaf (⟨3,1,-4,-1⟩)) (.leaf (⟨-5,-2,8,3⟩))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (⟨-5,-3,7,4⟩)) (.branch 32 (.leaf (⟨5,4,-9,-7⟩)) (.leaf (⟨-6,1,11,-2⟩)))) (.branch 35 (.branch 34 (.leaf (⟨1,7,-2,-13⟩)) (.leaf (⟨1,-3,-1,4⟩))) (.branch 36 (.leaf (⟨-3,-4,4,5⟩)) (.leaf (⟨-6,-5,11,9⟩))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (⟨7,-1,-13,2⟩)) (.leaf (⟨-1,-8,2,15⟩))) (.branch 40 (.leaf (⟨-4,3,5,-4⟩)) (.leaf (⟨3,7,-4,-9⟩)))) (.branch 43 (.branch 42 (.leaf (⟨-5,6,9,-11⟩)) (.leaf (⟨6,11,-11,-20⟩))) (.branch 44 (.leaf (⟨7,6,-13,-11⟩)) (.leaf (⟨-8,1,15,-2⟩)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (⟨1,9,-2,-17⟩)) (.branch 47 (.leaf (⟨-4,-1,5,1⟩)) (.leaf (⟨7,-3,-9,4⟩)))) (.branch 50 (.branch 49 (.leaf (⟨-3,-10,4,13⟩)) (.leaf (⟨13,10,-17,-13⟩))) (.branch 51 (.leaf (⟨-10,3,13,-4⟩)) (.leaf (⟨-10,-7,13,9⟩))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (⟨-8,-7,15,13⟩)) (.leaf (⟨15,7,-28,-13⟩))) (.branch 55 (.leaf (⟨-7,8,13,-15⟩)) (.leaf (⟨7,4,-9,-5⟩)))) (.branch 58 (.branch 57 (.leaf (⟨3,13,-4,-17⟩)) (.leaf (⟨11,5,-20,-9⟩))) (.branch 59 (.leaf (⟨8,15,-15,-28⟩)) (.leaf (⟨9,8,-17,-15⟩))))))))
noncomputable def liftMatrix (p : Fin 60) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 60) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],4⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],5⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],6⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],7⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],8⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],9⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],10⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],11⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],12⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],13⟩,⟨⟨3,-1,-5,2⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-1)],14⟩,⟨⟨-1,-4,2,7⟩,[.t (-1),.s,.t (-2),.s,.t (3)],15⟩,⟨⟨-1,2,1,-3⟩,[.t (-1),.s,.t (-3)],16⟩,⟨⟨2,3,-3,-4⟩,[.t (-1),.s,.t (-3),.s,.t (1)],17⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],18⟩,⟨⟨-4,1,7,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-1)],19⟩,⟨⟨1,5,-2,-9⟩,[.t (-1),.s,.t (-2),.s,.t (4)],20⟩,⟨⟨3,-2,-4,3⟩,[.t (-1),.s,.t (-4),.s,.t (-1)],21⟩,⟨⟨-2,-5,3,7⟩,[.t (-1),.s,.t (-3),.s,.t (2)],22⟩,⟨⟨2,-3,-3,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2)],23⟩,⟨⟨-3,-5,5,8⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (1)],24⟩,⟨⟨-4,-3,7,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],25⟩,⟨⟨5,-1,-9,2⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],26⟩,⟨⟨-1,-6,2,11⟩,[.t (-1),.s,.t (-2),.s,.t (5)],27⟩,⟨⟨3,1,-4,-1⟩,[.t (-1),.s,.t (-4),.s,.t (0)],28⟩,⟨⟨-5,-2,8,3⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (0)],29⟩,⟨⟨-5,-3,7,4⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (0)],30⟩,⟨⟨5,4,-9,-7⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],31⟩,⟨⟨-6,1,11,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],32⟩,⟨⟨1,7,-2,-13⟩,[.t (-1),.s,.t (-2),.s,.t (6)],33⟩,⟨⟨1,-3,-1,4⟩,[.t (-1),.s,.t (-4)],34⟩,⟨⟨-3,-4,4,5⟩,[.t (-1),.s,.t (-4),.s,.t (1)],35⟩,⟨⟨-6,-5,11,9⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],36⟩,⟨⟨7,-1,-13,2⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],37⟩,⟨⟨-1,-8,2,15⟩,[.t (-1),.s,.t (-2),.s,.t (7)],38⟩,⟨⟨-4,3,5,-4⟩,[.t (-1),.s,.t (-5),.s,.t (-1)],39⟩,⟨⟨3,7,-4,-9⟩,[.t (-1),.s,.t (-4),.s,.t (2)],40⟩,⟨⟨-5,6,9,-11⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],41⟩,⟨⟨6,11,-11,-20⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],42⟩,⟨⟨7,6,-13,-11⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],43⟩,⟨⟨-8,1,15,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],44⟩,⟨⟨1,9,-2,-17⟩,[.t (-1),.s,.t (-2),.s,.t (8)],45⟩,⟨⟨-4,-1,5,1⟩,[.t (-1),.s,.t (-5),.s,.t (0)],46⟩,⟨⟨7,-3,-9,4⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (-1)],47⟩,⟨⟨-3,-10,4,13⟩,[.t (-1),.s,.t (-4),.s,.t (3)],48⟩,⟨⟨13,10,-17,-13⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],49⟩,⟨⟨-10,3,13,-4⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-1)],50⟩,⟨⟨-10,-7,13,9⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (0)],51⟩,⟨⟨-8,-7,15,13⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],52⟩,⟨⟨15,7,-28,-13⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],53⟩,⟨⟨-7,8,13,-15⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],54⟩,⟨⟨7,4,-9,-5⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (0)],55⟩,⟨⟨3,13,-4,-17⟩,[.t (-1),.s,.t (-4),.s,.t (4)],56⟩,⟨⟨11,5,-20,-9⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],57⟩,⟨⟨8,15,-15,-28⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],58⟩,⟨⟨9,8,-17,-15⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],59⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 60 ∧ ((List.finRange 60).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 60) := [⟨4,1,⟨⟨1,2,0,1⟩,[.t (2)],0⟩⟩,⟨46,9,⟨⟨39,32,-50,-41⟩,[.t (-1),.s,.t (-5),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨55,9,⟨⟨-41,-32,50,39⟩,[.t (-1),.s,.t (-6),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨51,7,⟨⟨-145,-112,268,207⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨49,6,⟨⟨245,188,-447,-343⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨56,10,⟨⟨-129,-98,233,177⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-8),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨30,4,⟨⟨41,30,-67,-49⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨22,3,⟨⟨-29,-20,45,31⟩,[.t (-1),.s,.t (-3),.s,.t (-6),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨29,3,⟨⟨31,20,-45,-29⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨24,4,⟨⟨-49,-30,67,41⟩,[.t (-1),.s,.t (-4),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨25,5,⟨⟨55,32,-98,-57⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨31,5,⟨⟨-57,-32,98,55⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-5),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨57,10,⟨⟨177,98,-233,-129⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨42,6,⟨⟨-343,-188,447,245⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-6),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨43,7,⟨⟨207,112,-268,-145⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (-3),.s,.t (-7),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨53,8,⟨⟨145,78,-277,-149⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-8),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨58,11,⟨⟨-359,-192,675,361⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-8),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨59,11,⟨⟨361,192,-675,-359⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-9),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨45,8,⟨⟨-149,-78,277,145⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-12),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨6,2,⟨⟨1,0,3,1⟩,[.t (0),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨7,2,⟨⟨1,0,-3,1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨2,1,⟨⟨1,-2,0,1⟩,[.t (-2)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-4,5),(-7,9),(-10,13),(-13,17),(-3,4),(-5,7),(-2,3),(-5,8),(-3,5),(-4,7),(-5,9),(-11,20),(-6,11),(-7,13),(-15,28),(-8,15),(-9,17),(-1,2),(0,1),(1,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G240_93_c2

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
