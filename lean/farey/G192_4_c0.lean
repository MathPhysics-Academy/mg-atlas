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
namespace G192_4_c0
noncomputable def originalSData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (8))) (.branch 7 (.leaf (12)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (13))) (.branch 11 (.leaf (16)) (.leaf (18)))) (.branch 14 (.branch 13 (.leaf (15)) (.leaf (21))) (.branch 15 (.leaf (2)) (.leaf (24)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (22)) (.leaf (26))) (.branch 19 (.leaf (23)) (.leaf (28)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (4))) (.branch 23 (.leaf (30)) (.leaf (32))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (34))) (.branch 27 (.leaf (31)) (.leaf (37)))) (.branch 30 (.branch 29 (.leaf (33)) (.leaf (40))) (.branch 31 (.leaf (10)) (.leaf (43))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (11)) (.leaf (20))) (.branch 35 (.leaf (42)) (.leaf (45)))) (.branch 38 (.branch 37 (.leaf (47)) (.leaf (44))) (.branch 39 (.leaf (46)) (.leaf (50))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (39)) (.leaf (35))) (.branch 43 (.leaf (52)) (.leaf (17)))) (.branch 46 (.branch 45 (.leaf (55)) (.leaf (53))) (.branch 47 (.leaf (56)) (.leaf (54)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (59)) (.leaf (61))) (.branch 51 (.leaf (29)) (.leaf (63)))) (.branch 54 (.branch 53 (.leaf (25)) (.leaf (41))) (.branch 55 (.leaf (66)) (.leaf (27))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (65)) (.leaf (69))) (.branch 59 (.leaf (71)) (.leaf (67)))) (.branch 62 (.branch 61 (.leaf (74)) (.leaf (68))) (.branch 63 (.leaf (76)) (.leaf (57)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (78)) (.leaf (38))) (.branch 67 (.leaf (36)) (.leaf (81)))) (.branch 70 (.branch 69 (.leaf (83)) (.leaf (51))) (.branch 71 (.leaf (85)) (.leaf (80))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (86)) (.leaf (88))) (.branch 75 (.leaf (82)) (.leaf (91)))) (.branch 78 (.branch 77 (.leaf (84)) (.leaf (93))) (.branch 79 (.leaf (70)) (.leaf (62)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (96)) (.leaf (48))) (.branch 83 (.leaf (99)) (.leaf (49)))) (.branch 86 (.branch 85 (.leaf (79)) (.leaf (64))) (.branch 87 (.leaf (97)) (.leaf (104))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (98)) (.leaf (106))) (.branch 91 (.leaf (89)) (.leaf (100)))) (.branch 94 (.branch 93 (.leaf (75)) (.leaf (101))) (.branch 95 (.leaf (110)) (.leaf (109))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (58)) (.leaf (111))) (.branch 99 (.leaf (113)) (.leaf (60)))) (.branch 102 (.branch 101 (.leaf (92)) (.leaf (115))) (.branch 103 (.leaf (108)) (.leaf (94))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (112)) (.leaf (119))) (.branch 107 (.leaf (114)) (.leaf (121)))) (.branch 110 (.branch 109 (.leaf (95)) (.leaf (102))) (.branch 111 (.leaf (116)) (.leaf (72)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (123)) (.leaf (73))) (.branch 115 (.leaf (90)) (.leaf (77)))) (.branch 118 (.branch 117 (.leaf (103)) (.leaf (125))) (.branch 119 (.leaf (117)) (.leaf (124))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (126)) (.leaf (120))) (.branch 123 (.leaf (118)) (.leaf (87)))) (.branch 126 (.branch 125 (.leaf (127)) (.leaf (122))) (.branch 127 (.leaf (107)) (.leaf (105)))))))))
noncomputable def originalS (p : Fin 128) : Fin 128 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (10)) (.leaf (11))) (.branch 7 (.leaf (0)) (.leaf (13))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (15)) (.leaf (12))) (.branch 11 (.leaf (17)) (.leaf (19)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (22))) (.branch 15 (.leaf (23)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (25)) (.leaf (27))) (.branch 19 (.leaf (1)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (29)) (.leaf (24))) (.branch 23 (.leaf (31)) (.leaf (33))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (28)) (.leaf (35))) (.branch 27 (.leaf (36)) (.leaf (38)))) (.branch 30 (.branch 29 (.leaf (39)) (.leaf (41))) (.branch 31 (.leaf (42)) (.leaf (44))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (7)) (.leaf (14))) (.branch 35 (.leaf (9)) (.leaf (46)))) (.branch 38 (.branch 37 (.leaf (48)) (.leaf (49))) (.branch 39 (.leaf (50)) (.leaf (45))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (32)) (.leaf (51))) (.branch 43 (.leaf (53)) (.leaf (54)))) (.branch 46 (.branch 45 (.leaf (56)) (.leaf (57))) (.branch 47 (.leaf (58)) (.leaf (16)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (60)) (.leaf (62))) (.branch 51 (.leaf (18)) (.leaf (64)))) (.branch 54 (.branch 53 (.leaf (21)) (.leaf (65))) (.branch 55 (.leaf (67)) (.leaf (68))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (40)) (.leaf (70))) (.branch 59 (.leaf (72)) (.leaf (73)))) (.branch 62 (.branch 61 (.leaf (75)) (.leaf (26))) (.branch 63 (.leaf (77)) (.leaf (52)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (79)) (.leaf (80))) (.branch 67 (.leaf (30)) (.leaf (82)))) (.branch 70 (.branch 69 (.leaf (84)) (.leaf (34))) (.branch 71 (.leaf (76)) (.leaf (37))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (87)) (.leaf (89))) (.branch 75 (.leaf (90)) (.leaf (61)))) (.branch 78 (.branch 77 (.leaf (92)) (.leaf (94))) (.branch 79 (.leaf (95)) (.leaf (91)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (97)) (.leaf (98))) (.branch 83 (.leaf (100)) (.leaf (43)))) (.branch 86 (.branch 85 (.leaf (101)) (.leaf (102))) (.branch 87 (.leaf (103)) (.leaf (105))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (47)) (.leaf (59))) (.branch 91 (.leaf (107)) (.leaf (108)))) (.branch 94 (.branch 93 (.leaf (109)) (.leaf (78))) (.branch 95 (.leaf (71)) (.leaf (74))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (55)) (.leaf (112))) (.branch 99 (.leaf (114)) (.leaf (106)))) (.branch 102 (.branch 101 (.leaf (83)) (.leaf (116))) (.branch 103 (.leaf (99)) (.leaf (117))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (118)) (.leaf (119))) (.branch 107 (.leaf (120)) (.leaf (104)))) (.branch 110 (.branch 109 (.leaf (69)) (.leaf (63))) (.branch 111 (.leaf (122)) (.leaf (110)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (124)) (.leaf (66))) (.branch 115 (.leaf (81)) (.leaf (85)))) (.branch 118 (.branch 117 (.leaf (96)) (.leaf (86))) (.branch 119 (.leaf (93)) (.leaf (126))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (123)) (.leaf (113))) (.branch 123 (.leaf (111)) (.leaf (125)))) (.branch 126 (.branch 125 (.leaf (127)) (.leaf (115))) (.branch 127 (.leaf (88)) (.leaf (121)))))))))
noncomputable def originalT (p : Fin 128) : Fin 128 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 64) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (9)) (.leaf (3))) (.branch 15 (.leaf (4)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (12)) (.leaf (13)))) (.branch 22 (.branch 21 (.leaf (14)) (.leaf (6))) (.branch 23 (.leaf (7)) (.leaf (8))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (9)) (.leaf (15))) (.branch 27 (.leaf (16)) (.leaf (17)))) (.branch 30 (.branch 29 (.leaf (14)) (.leaf (18))) (.branch 31 (.leaf (10)) (.leaf (11))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (12)) (.leaf (13))) (.branch 35 (.leaf (19)) (.leaf (20)))) (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (18))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (24)) (.leaf (25))) (.branch 43 (.leaf (15)) (.leaf (16)))) (.branch 46 (.branch 45 (.leaf (17)) (.leaf (25))) (.branch 47 (.leaf (26)) (.leaf (27)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (28)) (.leaf (29))) (.branch 51 (.leaf (24)) (.leaf (30)))) (.branch 54 (.branch 53 (.leaf (19)) (.leaf (20))) (.branch 55 (.leaf (21)) (.leaf (22))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (23)) (.leaf (30))) (.branch 59 (.leaf (31)) (.leaf (32)))) (.branch 62 (.branch 61 (.leaf (33)) (.leaf (34))) (.branch 63 (.leaf (35)) (.leaf (36)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (37)) (.leaf (26))) (.branch 67 (.leaf (27)) (.leaf (28)))) (.branch 70 (.branch 69 (.leaf (29)) (.leaf (36))) (.branch 71 (.leaf (37)) (.leaf (38))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (39)) (.leaf (40))) (.branch 75 (.leaf (41)) (.leaf (42)))) (.branch 78 (.branch 77 (.leaf (43)) (.leaf (44))) (.branch 79 (.leaf (45)) (.leaf (43)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (31)) (.leaf (32))) (.branch 83 (.leaf (33)) (.leaf (34)))) (.branch 86 (.branch 85 (.leaf (35)) (.leaf (45))) (.branch 87 (.leaf (46)) (.leaf (47))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (48)) (.leaf (49))) (.branch 91 (.leaf (50)) (.leaf (51)))) (.branch 94 (.branch 93 (.leaf (51)) (.leaf (52))) (.branch 95 (.leaf (53)) (.leaf (54))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (38)) (.leaf (39))) (.branch 99 (.leaf (40)) (.leaf (41)))) (.branch 102 (.branch 101 (.leaf (42)) (.leaf (44))) (.branch 103 (.leaf (54)) (.leaf (55))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (56)) (.leaf (57))) (.branch 107 (.leaf (50)) (.leaf (58)))) (.branch 110 (.branch 109 (.leaf (59)) (.leaf (59))) (.branch 111 (.leaf (55)) (.leaf (46)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (47)) (.leaf (48))) (.branch 115 (.leaf (49)) (.leaf (52)))) (.branch 118 (.branch 117 (.leaf (53)) (.leaf (60))) (.branch 119 (.leaf (61)) (.leaf (62))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (58)) (.leaf (63))) (.branch 123 (.leaf (60)) (.leaf (56)))) (.branch 126 (.branch 125 (.leaf (57)) (.leaf (61))) (.branch 127 (.leaf (63)) (.leaf (62)))))))))
noncomputable def projection (p : Fin 128) : Fin 64 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 128) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (6))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (11)) (.leaf (12))) (.branch 11 (.leaf (16)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (18)) (.leaf (19))) (.branch 15 (.leaf (20)) (.leaf (25)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (26)) (.leaf (27))) (.branch 19 (.leaf (29)) (.leaf (34)))) (.branch 22 (.branch 21 (.leaf (35)) (.leaf (36))) (.branch 23 (.leaf (37)) (.leaf (38))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (40)) (.leaf (41))) (.branch 27 (.leaf (46)) (.leaf (47)))) (.branch 30 (.branch 29 (.leaf (48)) (.leaf (49))) (.branch 31 (.leaf (51)) (.leaf (58))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (59)) (.leaf (60))) (.branch 35 (.leaf (61)) (.leaf (62)))) (.branch 38 (.branch 37 (.leaf (63)) (.leaf (64))) (.branch 39 (.leaf (71)) (.leaf (72))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (73)) (.leaf (74))) (.branch 43 (.leaf (75)) (.leaf (76)))) (.branch 46 (.branch 45 (.leaf (77)) (.leaf (78))) (.branch 47 (.leaf (86)) (.leaf (87)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (88)) (.leaf (89))) (.branch 51 (.leaf (90)) (.leaf (91)))) (.branch 54 (.branch 53 (.leaf (93)) (.leaf (94))) (.branch 55 (.leaf (95)) (.leaf (103))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (104)) (.leaf (105))) (.branch 59 (.leaf (107)) (.leaf (108)))) (.branch 62 (.branch 61 (.leaf (117)) (.leaf (118))) (.branch 63 (.leaf (119)) (.leaf (121))))))))
noncomputable def representative (p : Fin 64) : Fin 128 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (5))) (.branch 11 (.leaf (7)) (.leaf (16)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (14))) (.branch 15 (.leaf (13)) (.leaf (19)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (11)) (.leaf (22))) (.branch 19 (.leaf (24)) (.leaf (15)))) (.branch 22 (.branch 21 (.leaf (25)) (.leaf (27))) (.branch 23 (.leaf (17)) (.leaf (26))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (18)) (.leaf (20))) (.branch 27 (.leaf (23)) (.leaf (21)))) (.branch 30 (.branch 29 (.leaf (32)) (.leaf (34))) (.branch 31 (.leaf (36)) (.leaf (38))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (28)) (.leaf (41))) (.branch 35 (.leaf (29)) (.leaf (43)))) (.branch 38 (.branch 37 (.leaf (30)) (.leaf (45))) (.branch 39 (.leaf (31)) (.leaf (46))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (48)) (.leaf (33))) (.branch 43 (.leaf (51)) (.leaf (35)))) (.branch 46 (.branch 45 (.leaf (52)) (.leaf (37))) (.branch 47 (.leaf (39)) (.leaf (56)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (40)) (.leaf (50))) (.branch 51 (.leaf (49)) (.leaf (42)))) (.branch 54 (.branch 53 (.leaf (44)) (.leaf (55))) (.branch 55 (.leaf (59)) (.leaf (53))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (47)) (.leaf (62))) (.branch 59 (.leaf (63)) (.leaf (54)))) (.branch 62 (.branch 61 (.leaf (61)) (.leaf (60))) (.branch 63 (.leaf (57)) (.leaf (58))))))))
noncomputable def S (p : Fin 64) : Fin 64 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (9)) (.leaf (11))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (13)) (.leaf (14))) (.branch 11 (.leaf (15)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (4))) (.branch 15 (.leaf (18)) (.leaf (20)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (21)) (.leaf (23))) (.branch 19 (.leaf (25)) (.leaf (6)))) (.branch 22 (.branch 21 (.leaf (26)) (.leaf (28))) (.branch 23 (.leaf (29)) (.leaf (24))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (12)) (.leaf (30))) (.branch 27 (.leaf (31)) (.leaf (10)))) (.branch 30 (.branch 29 (.leaf (33)) (.leaf (35))) (.branch 31 (.leaf (37)) (.leaf (39))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (40)) (.leaf (42))) (.branch 35 (.leaf (16)) (.leaf (44)))) (.branch 38 (.branch 37 (.leaf (19)) (.leaf (43))) (.branch 39 (.leaf (22)) (.leaf (47))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (49)) (.leaf (50))) (.branch 43 (.leaf (34)) (.leaf (51)))) (.branch 46 (.branch 45 (.leaf (53)) (.leaf (54))) (.branch 47 (.leaf (55)) (.leaf (57)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (27)) (.leaf (32))) (.branch 51 (.leaf (58)) (.leaf (59)))) (.branch 54 (.branch 53 (.leaf (45)) (.leaf (38))) (.branch 55 (.leaf (41)) (.leaf (60))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (61)) (.leaf (62))) (.branch 59 (.leaf (56)) (.leaf (36)))) (.branch 62 (.branch 61 (.leaf (46)) (.leaf (52))) (.branch 63 (.leaf (63)) (.leaf (48))))))))
noncomputable def T (p : Fin 64) : Fin 64 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (5)) (.leaf (12))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (13)) (.leaf (2))) (.branch 7 (.leaf (19)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (6))) (.branch 11 (.leaf (27)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (24)) (.leaf (8))) (.branch 15 (.leaf (9)) (.leaf (10)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (34)) (.leaf (11))) (.branch 19 (.leaf (14)) (.leaf (36)))) (.branch 22 (.branch 21 (.leaf (15)) (.leaf (16))) (.branch 23 (.leaf (38)) (.leaf (17))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (23)) (.leaf (18))) (.branch 27 (.leaf (20)) (.leaf (48)))) (.branch 30 (.branch 29 (.leaf (21)) (.leaf (22))) (.branch 31 (.leaf (25)) (.leaf (26))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (49)) (.leaf (28))) (.branch 35 (.leaf (42)) (.leaf (29)))) (.branch 38 (.branch 37 (.leaf (59)) (.leaf (30))) (.branch 39 (.leaf (53)) (.leaf (31))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (32)) (.leaf (54))) (.branch 43 (.leaf (33)) (.leaf (37)))) (.branch 46 (.branch 45 (.leaf (35)) (.leaf (52))) (.branch 47 (.leaf (60)) (.leaf (39)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (63)) (.leaf (40))) (.branch 51 (.leaf (41)) (.leaf (43)))) (.branch 54 (.branch 53 (.leaf (61)) (.leaf (44))) (.branch 55 (.leaf (45)) (.leaf (46))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (58)) (.leaf (47))) (.branch 59 (.leaf (50)) (.leaf (51)))) (.branch 62 (.branch 61 (.leaf (55)) (.leaf (56))) (.branch 63 (.leaf (57)) (.leaf (62))))))))
noncomputable def Ti (p : Fin 64) : Fin 64 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 64) : Fin 64 := T (S p)
theorem quotient_relations : (∀ p : Fin 64, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 128, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 128, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 64, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 64)) := [[0,3,9],[1,2,8],[4,5,14],[6,7,15],[10,11,21],[12,13,18],[16,17,29],[19,20,30],[22,23,31],[24,25,26],[27,28,40],[32,33,50],[34,35,51],[36,37,54],[38,39,55],[41,42,59],[43,44,45],[46,47,61],[48,49,58],[52,53,60],[56,57,63],[62]]
noncomputable def verticesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (12)) (.leaf (13)))) (.branch 14 (.branch 13 (.leaf (15)) (.leaf (16))) (.branch 15 (.leaf (8)) (.leaf (11)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (18)) (.leaf (19))) (.branch 19 (.leaf (17)) (.leaf (21)))) (.branch 22 (.branch 21 (.leaf (22)) (.leaf (14))) (.branch 23 (.leaf (24)) (.leaf (25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (27)) (.leaf (28))) (.branch 27 (.leaf (29)) (.leaf (30)))) (.branch 30 (.branch 29 (.leaf (31)) (.leaf (20))) (.branch 31 (.leaf (23)) (.leaf (26))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (33)) (.leaf (34))) (.branch 35 (.leaf (36)) (.leaf (37)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (40))) (.branch 39 (.leaf (42)) (.leaf (43))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (32)) (.leaf (45))) (.branch 43 (.leaf (46)) (.leaf (48)))) (.branch 46 (.branch 45 (.leaf (49)) (.leaf (50))) (.branch 47 (.leaf (51)) (.leaf (52)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (54)) (.leaf (55))) (.branch 51 (.leaf (35)) (.leaf (38)))) (.branch 54 (.branch 53 (.leaf (57)) (.leaf (58))) (.branch 55 (.leaf (41)) (.leaf (44))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (60)) (.leaf (61))) (.branch 59 (.leaf (56)) (.leaf (47)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (53))) (.branch 63 (.leaf (63)) (.leaf (62))))))))
noncomputable def verticesIndex (p : Fin 64) : Fin 64 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (9)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (15)))) (.branch 14 (.branch 13 (.leaf (10)) (.leaf (11))) (.branch 15 (.leaf (21)) (.leaf (12)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (13)) (.leaf (18))) (.branch 19 (.leaf (16)) (.leaf (17)))) (.branch 22 (.branch 21 (.leaf (29)) (.leaf (19))) (.branch 23 (.leaf (20)) (.leaf (30))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (22)) (.leaf (23))) (.branch 27 (.leaf (31)) (.leaf (24)))) (.branch 30 (.branch 29 (.leaf (25)) (.leaf (26))) (.branch 31 (.leaf (27)) (.leaf (28))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (40)) (.leaf (32))) (.branch 35 (.leaf (33)) (.leaf (50)))) (.branch 38 (.branch 37 (.leaf (34)) (.leaf (35))) (.branch 39 (.leaf (51)) (.leaf (36))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (54))) (.branch 43 (.leaf (38)) (.leaf (39)))) (.branch 46 (.branch 45 (.leaf (55)) (.leaf (41))) (.branch 47 (.leaf (42)) (.leaf (59)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (43)) (.leaf (44))) (.branch 51 (.leaf (45)) (.leaf (46)))) (.branch 54 (.branch 53 (.leaf (47)) (.leaf (61))) (.branch 55 (.leaf (48)) (.leaf (49))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (58)) (.leaf (52))) (.branch 59 (.leaf (53)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (56)) (.leaf (57))) (.branch 63 (.leaf (63)) (.leaf (62))))))))
noncomputable def verticesBack (p : Fin 64) : Fin 64 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 64, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 64 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 64, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 64)) := [[0,1],[2,4],[3,6],[5,9],[7,10],[8,12],[11,16],[13,14],[15,19],[17,22],[18,24],[20,25],[21,27],[23,26],[28,32],[29,34],[30,36],[31,38],[33,41],[35,43],[37,45],[39,46],[40,48],[42,51],[44,52],[47,56],[49,50],[53,55],[54,59],[57,62],[58,63],[60,61]]
noncomputable def edgesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (8))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (7))) (.branch 11 (.leaf (9)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (14))) (.branch 15 (.leaf (15)) (.leaf (16)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (13)) (.leaf (18))) (.branch 19 (.leaf (20)) (.leaf (17)))) (.branch 22 (.branch 21 (.leaf (22)) (.leaf (24))) (.branch 23 (.leaf (19)) (.leaf (26))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (23))) (.branch 27 (.leaf (27)) (.leaf (25)))) (.branch 30 (.branch 29 (.leaf (28)) (.leaf (30))) (.branch 31 (.leaf (32)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (29)) (.leaf (36))) (.branch 35 (.leaf (31)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (40))) (.branch 39 (.leaf (35)) (.leaf (42))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (44)) (.leaf (37))) (.branch 43 (.leaf (46)) (.leaf (39)))) (.branch 46 (.branch 45 (.leaf (48)) (.leaf (41))) (.branch 47 (.leaf (43)) (.leaf (50)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (45)) (.leaf (52))) (.branch 51 (.leaf (53)) (.leaf (47)))) (.branch 54 (.branch 53 (.leaf (49)) (.leaf (54))) (.branch 55 (.leaf (56)) (.leaf (55))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (51)) (.leaf (58))) (.branch 59 (.leaf (60)) (.leaf (57)))) (.branch 62 (.branch 61 (.leaf (62)) (.leaf (63))) (.branch 63 (.leaf (59)) (.leaf (61))))))))
noncomputable def edgesIndex (p : Fin 64) : Fin 64 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (9))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (10))) (.branch 11 (.leaf (8)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (16))) (.branch 15 (.leaf (13)) (.leaf (14)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (15)) (.leaf (19))) (.branch 19 (.leaf (17)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (18)) (.leaf (24))) (.branch 23 (.leaf (20)) (.leaf (25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (27))) (.branch 27 (.leaf (23)) (.leaf (26)))) (.branch 30 (.branch 29 (.leaf (28)) (.leaf (32))) (.branch 31 (.leaf (29)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (30)) (.leaf (36))) (.branch 35 (.leaf (31)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (41))) (.branch 39 (.leaf (35)) (.leaf (43))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (45))) (.branch 43 (.leaf (39)) (.leaf (46)))) (.branch 46 (.branch 45 (.leaf (40)) (.leaf (48))) (.branch 47 (.leaf (42)) (.leaf (51)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (44)) (.leaf (52))) (.branch 51 (.leaf (47)) (.leaf (56)))) (.branch 54 (.branch 53 (.leaf (49)) (.leaf (50))) (.branch 55 (.leaf (53)) (.leaf (55))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (54)) (.leaf (59))) (.branch 59 (.leaf (57)) (.leaf (62)))) (.branch 62 (.branch 61 (.leaf (58)) (.leaf (63))) (.branch 63 (.leaf (60)) (.leaf (61))))))))
noncomputable def edgesBack (p : Fin 64) : Fin 64 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 64, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 64 := by decide +kernel
theorem edges_partition : ∀ p : Fin 64, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 64)) := [[0,2,5],[1,3,7,11,17,23,24,12],[4,8,13],[6,9,14,18,25,30,37,43,51,59,36,19],[10,15,20,26,31,39,47,57,62,63,48,27],[16,21,28,33,42,34],[22,29,35,44,53,38],[32,40,49],[41,50,58,56,61,52,45,54],[46,55,60]]
noncomputable def facesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (11)) (.leaf (2))) (.branch 7 (.leaf (14)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (15))) (.branch 11 (.leaf (26)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (10)) (.leaf (13))) (.branch 15 (.leaf (16)) (.leaf (27)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (38)) (.leaf (7))) (.branch 19 (.leaf (17)) (.leaf (25)))) (.branch 22 (.branch 21 (.leaf (28)) (.leaf (39))) (.branch 23 (.leaf (44)) (.leaf (8))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (9)) (.leaf (18))) (.branch 27 (.leaf (29)) (.leaf (37)))) (.branch 30 (.branch 29 (.leaf (40)) (.leaf (45))) (.branch 31 (.leaf (19)) (.leaf (30))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (50)) (.leaf (41))) (.branch 35 (.leaf (43)) (.leaf (46)))) (.branch 38 (.branch 37 (.leaf (24)) (.leaf (20))) (.branch 39 (.leaf (49)) (.leaf (31))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (51)) (.leaf (53))) (.branch 43 (.leaf (42)) (.leaf (21)))) (.branch 46 (.branch 45 (.leaf (47)) (.leaf (59))) (.branch 47 (.leaf (61)) (.leaf (32)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (36)) (.leaf (52))) (.branch 51 (.leaf (54)) (.leaf (22)))) (.branch 54 (.branch 53 (.leaf (58)) (.leaf (48))) (.branch 55 (.leaf (60)) (.leaf (62))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (56)) (.leaf (33))) (.branch 59 (.leaf (55)) (.leaf (23)))) (.branch 62 (.branch 61 (.leaf (63)) (.leaf (57))) (.branch 63 (.leaf (34)) (.leaf (35))))))))
noncomputable def facesIndex (p : Fin 64) : Fin 64 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (7))) (.branch 7 (.leaf (11)) (.leaf (17))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (23)) (.leaf (24))) (.branch 11 (.leaf (12)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (13))) (.branch 15 (.leaf (6)) (.leaf (9)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (18))) (.branch 19 (.leaf (25)) (.leaf (30)))) (.branch 22 (.branch 21 (.leaf (37)) (.leaf (43))) (.branch 23 (.leaf (51)) (.leaf (59))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (36)) (.leaf (19))) (.branch 27 (.leaf (10)) (.leaf (15)))) (.branch 30 (.branch 29 (.leaf (20)) (.leaf (26))) (.branch 31 (.leaf (31)) (.leaf (39))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (47)) (.leaf (57))) (.branch 35 (.leaf (62)) (.leaf (63)))) (.branch 38 (.branch 37 (.leaf (48)) (.leaf (27))) (.branch 39 (.leaf (16)) (.leaf (21))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (28)) (.leaf (33))) (.branch 43 (.leaf (42)) (.leaf (34)))) (.branch 46 (.branch 45 (.leaf (22)) (.leaf (29))) (.branch 47 (.leaf (35)) (.leaf (44)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (53)) (.leaf (38))) (.branch 51 (.leaf (32)) (.leaf (40)))) (.branch 54 (.branch 53 (.leaf (49)) (.leaf (41))) (.branch 55 (.leaf (50)) (.leaf (58))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (56)) (.leaf (61))) (.branch 59 (.leaf (52)) (.leaf (45)))) (.branch 62 (.branch 61 (.leaf (54)) (.leaf (46))) (.branch 63 (.leaf (55)) (.leaf (60))))))))
noncomputable def facesBack (p : Fin 64) : Fin 64 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 64, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 64 := by decide +kernel
theorem faces_partition : ∀ p : Fin 64, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [3,8,3,12,12,6,6,3,8,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 1 : Int) = 22 - 32 + 10 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 1 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.leaf (⟨0,1,-1,-2⟩))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 11 (.leaf (⟨1,0,-2,1⟩)) (.leaf (⟨0,-1,1,3⟩)))) (.branch 14 (.branch 13 (.leaf (⟨0,1,-1,1⟩)) (.leaf (⟨1,1,1,2⟩))) (.branch 15 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨1,1,-2,-1⟩)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (⟨-1,0,3,-1⟩)) (.leaf (⟨0,1,-1,-4⟩))) (.branch 19 (.leaf (⟨1,0,2,1⟩)) (.leaf (⟨1,-1,-1,2⟩)))) (.branch 22 (.branch 21 (.leaf (⟨-1,-2,2,3⟩)) (.leaf (⟨-1,-1,3,2⟩))) (.branch 23 (.leaf (⟨1,0,4,1⟩)) (.leaf (⟨0,1,-1,3⟩))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (⟨0,-1,1,-2⟩)) (.leaf (⟨-1,-1,-2,-3⟩))) (.branch 27 (.leaf (⟨-1,0,-3,-1⟩)) (.leaf (⟨-1,1,2,-3⟩)))) (.branch 30 (.branch 29 (.leaf (⟨1,2,-3,-5⟩)) (.leaf (⟨1,1,-4,-3⟩))) (.branch 31 (.leaf (⟨-2,-1,3,1⟩)) (.leaf (⟨1,1,3,4⟩))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (⟨2,-1,-5,3⟩)) (.leaf (⟨-1,-3,3,8⟩))) (.branch 35 (.leaf (⟨1,-1,-3,4⟩)) (.leaf (⟨-1,-2,4,7⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-1,2,1,-3⟩)) (.leaf (⟨2,3,-3,-4⟩))) (.branch 39 (.leaf (⟨1,-1,4,-3⟩)) (.leaf (⟨-1,-2,-3,-7⟩))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (⟨2,1,-5,-2⟩)) (.leaf (⟨-3,-4,4,5⟩))) (.branch 43 (.leaf (⟨-4,-1,5,1⟩)) (.leaf (⟨-2,-5,3,7⟩)))) (.branch 46 (.branch 45 (.leaf (⟨-5,-3,7,4⟩)) (.leaf (⟨3,-2,-4,3⟩))) (.branch 47 (.leaf (⟨-2,1,-7,3⟩)) (.leaf (⟨1,3,3,10⟩)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (⟨1,-2,-2,5⟩)) (.leaf (⟨-2,-3,5,7⟩))) (.branch 51 (.leaf (⟨-3,-2,8,5⟩)) (.leaf (⟨-2,-1,7,3⟩)))) (.branch 54 (.branch 53 (.leaf (⟨-3,5,4,-7⟩)) (.leaf (⟨5,8,-7,-11⟩))) (.branch 55 (.leaf (⟨3,1,-4,-1⟩)) (.leaf (⟨-2,-1,-7,-4⟩))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (⟨3,4,-7,-9⟩)) (.leaf (⟨4,1,-9,-2⟩))) (.branch 59 (.leaf (⟨-3,-1,7,2⟩)) (.leaf (⟨1,-3,-1,4⟩)))) (.branch 62 (.branch 61 (.leaf (⟨8,3,-11,-4⟩)) (.leaf (⟨3,2,10,7⟩))) (.branch 63 (.leaf (⟨1,-4,-2,9⟩)) (.leaf (⟨-1,3,2,-7⟩))))))))
noncomputable def liftMatrix (p : Fin 64) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 64) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],10⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],11⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],12⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],13⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],14⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],15⟩,⟨⟨-1,0,3,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],16⟩,⟨⟨0,1,-1,-4⟩,[.t (0),.s,.t (4)],17⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],18⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],19⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],20⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],21⟩,⟨⟨1,0,4,1⟩,[.t (0),.s,.t (-4),.s,.t (0)],22⟩,⟨⟨0,1,-1,3⟩,[.t (0),.s,.t (-3)],23⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],24⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],25⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],26⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],27⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],28⟩,⟨⟨1,1,-4,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],29⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],30⟩,⟨⟨1,1,3,4⟩,[.t (0),.s,.t (-3),.s,.t (1)],31⟩,⟨⟨2,-1,-5,3⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-1)],32⟩,⟨⟨-1,-3,3,8⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (2)],33⟩,⟨⟨1,-1,-3,4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2)],34⟩,⟨⟨-1,-2,4,7⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],35⟩,⟨⟨-1,2,1,-3⟩,[.t (-1),.s,.t (-3)],36⟩,⟨⟨2,3,-3,-4⟩,[.t (-1),.s,.t (-3),.s,.t (1)],37⟩,⟨⟨1,-1,4,-3⟩,[.t (0),.s,.t (-4),.s,.t (-1)],38⟩,⟨⟨-1,-2,-3,-7⟩,[.t (0),.s,.t (-3),.s,.t (2)],39⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],40⟩,⟨⟨-3,-4,4,5⟩,[.t (-1),.s,.t (-4),.s,.t (1)],41⟩,⟨⟨-4,-1,5,1⟩,[.t (-1),.s,.t (-5),.s,.t (0)],42⟩,⟨⟨-2,-5,3,7⟩,[.t (-1),.s,.t (-3),.s,.t (2)],43⟩,⟨⟨-5,-3,7,4⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (0)],44⟩,⟨⟨3,-2,-4,3⟩,[.t (-1),.s,.t (-4),.s,.t (-1)],45⟩,⟨⟨-2,1,-7,3⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (-1)],46⟩,⟨⟨1,3,3,10⟩,[.t (0),.s,.t (-3),.s,.t (3)],47⟩,⟨⟨1,-2,-2,5⟩,[.t (-1),.s,.t (-2),.s,.t (-3)],48⟩,⟨⟨-2,-3,5,7⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (1)],49⟩,⟨⟨-3,-2,8,5⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],50⟩,⟨⟨-2,-1,7,3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],51⟩,⟨⟨-3,5,4,-7⟩,[.t (-1),.s,.t (-4),.s,.t (-2)],52⟩,⟨⟨5,8,-7,-11⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (1)],53⟩,⟨⟨3,1,-4,-1⟩,[.t (-1),.s,.t (-4),.s,.t (0)],54⟩,⟨⟨-2,-1,-7,-4⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (0)],55⟩,⟨⟨3,4,-7,-9⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (1)],56⟩,⟨⟨4,1,-9,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-5),.s,.t (0)],57⟩,⟨⟨-3,-1,7,2⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (0)],58⟩,⟨⟨1,-3,-1,4⟩,[.t (-1),.s,.t (-4)],59⟩,⟨⟨8,3,-11,-4⟩,[.t (-1),.s,.t (-4),.s,.t (-3),.s,.t (0)],60⟩,⟨⟨3,2,10,7⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (0)],61⟩,⟨⟨1,-4,-2,9⟩,[.t (-1),.s,.t (-2),.s,.t (-5)],62⟩,⟨⟨-1,3,2,-7⟩,[.t (-1),.s,.t (-2),.s,.t (-4)],63⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 64 ∧ ((List.finRange 64).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 64) := [⟨9,1,⟨⟨-1,-3,0,-1⟩,[.t (3)],0⟩⟩,⟨42,7,⟨⟨-11,-9,38,31⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨41,5,⟨⟨19,15,-52,-41⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨60,11,⟨⟨-41,-30,-138,-101⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨53,10,⟨⟨25,18,93,67⟩,[.t (0),.s,.t (-4),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨43,6,⟨⟨17,12,-61,-43⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨20,4,⟨⟨-5,-3,-13,-8⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨62,-3,⟨⟨-46,-21,103,47⟩,[.t (-1),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨56,8,⟨⟨34,15,111,49⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨49,9,⟨⟨-29,-12,75,31⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨50,9,⟨⟨31,12,-75,-29⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨33,5,⟨⟨-41,-15,52,19⟩,[.t (-1),.s,.t (-5),.s,.t (-4),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨51,7,⟨⟨31,9,-38,-11⟩,[.t (-1),.s,.t (-6),.s,.t (-2),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨35,6,⟨⟨-43,-12,61,17⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨17,3,⟨⟨-1,0,-8,-1⟩,[.t (0),.s,.t (-8),.s,.t (0)],0⟩⟩,⟨22,3,⟨⟨-1,0,8,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨55,10,⟨⟨67,-18,-93,25⟩,[.t (-1),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨61,11,⟨⟨-101,30,138,-41⟩,[.t (-1),.s,.t (-4),.s,.t (-4),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨47,8,⟨⟨49,-15,-111,34⟩,[.t (-1),.s,.t (-2),.s,.t (-5),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨25,4,⟨⟨-8,3,13,-5⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨13,2,⟨⟨4,-3,3,-2⟩,[.t (1),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨14,2,⟨⟨-2,3,-3,4⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨5,1,⟨⟨-1,3,0,-1⟩,[.t (-3)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-4,5),(-3,4),(-8,11),(-5,7),(-2,3),(-1,2),(-4,9),(-3,7),(-2,5),(-3,8),(-1,3),(-2,7),(-1,4),(0,1),(1,4),(2,7),(3,10),(1,3),(1,2),(1,1),(2,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G192_4_c0

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
