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
namespace PSL2_17_c5
noncomputable def originalSData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (8))) (.branch 7 (.leaf (11)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (13))) (.branch 11 (.leaf (4)) (.leaf (15)))) (.branch 14 (.branch 13 (.leaf (19)) (.leaf (10))) (.branch 15 (.leaf (2)) (.leaf (21)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (23)) (.leaf (25))) (.branch 19 (.leaf (27)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (30)) (.leaf (6))) (.branch 23 (.leaf (33)) (.leaf (17))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (28)) (.leaf (16))) (.branch 27 (.leaf (36)) (.leaf (32)))) (.branch 30 (.branch 29 (.leaf (26)) (.leaf (39))) (.branch 31 (.leaf (34)) (.leaf (42))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (44)) (.leaf (12))) (.branch 35 (.leaf (46)) (.leaf (48)))) (.branch 38 (.branch 37 (.leaf (24)) (.leaf (51))) (.branch 39 (.leaf (53)) (.leaf (45))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (55)) (.leaf (40))) (.branch 43 (.leaf (47)) (.leaf (38)))) (.branch 46 (.branch 45 (.leaf (18)) (.leaf (58))) (.branch 47 (.leaf (20)) (.leaf (60)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (37)) (.leaf (61))) (.branch 51 (.leaf (43)) (.leaf (35)))) (.branch 54 (.branch 53 (.leaf (64)) (.leaf (50))) (.branch 55 (.leaf (66)) (.leaf (59))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (69)) (.leaf (71))) (.branch 59 (.leaf (29)) (.leaf (41)))) (.branch 62 (.branch 61 (.leaf (31)) (.leaf (52))) (.branch 63 (.leaf (74)) (.leaf (75)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (49)) (.leaf (73))) (.branch 67 (.leaf (63)) (.leaf (77)))) (.branch 70 (.branch 69 (.leaf (78)) (.leaf (68))) (.branch 71 (.leaf (80)) (.leaf (72))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (82)) (.leaf (62))) (.branch 75 (.leaf (65)) (.leaf (54)))) (.branch 78 (.branch 77 (.leaf (85)) (.leaf (76))) (.branch 79 (.leaf (56)) (.leaf (86)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (79)) (.leaf (88))) (.branch 83 (.leaf (57)) (.leaf (90)))) (.branch 86 (.branch 85 (.leaf (92)) (.leaf (67))) (.branch 87 (.leaf (70)) (.leaf (94))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (87)) (.leaf (96))) (.branch 91 (.leaf (84)) (.leaf (97)))) (.branch 94 (.branch 93 (.leaf (83)) (.leaf (99))) (.branch 95 (.leaf (81)) (.leaf (101))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (95)) (.leaf (93))) (.branch 99 (.leaf (104)) (.leaf (91)))) (.branch 102 (.branch 101 (.leaf (107)) (.leaf (89))) (.branch 103 (.leaf (110)) (.leaf (111))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (100)) (.leaf (114))) (.branch 107 (.leaf (116)) (.leaf (98)))) (.branch 110 (.branch 109 (.leaf (119)) (.leaf (121))) (.branch 111 (.leaf (109)) (.leaf (106)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (118)) (.leaf (112))) (.branch 115 (.leaf (108)) (.leaf (124)))) (.branch 118 (.branch 117 (.leaf (103)) (.leaf (113))) (.branch 119 (.leaf (117)) (.leaf (105))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (122)) (.leaf (102))) (.branch 123 (.leaf (115)) (.leaf (126)))) (.branch 126 (.branch 125 (.leaf (120)) (.leaf (127))) (.branch 127 (.leaf (125)) (.leaf (123)))))))))
noncomputable def originalS (p : Fin 128) : Fin 128 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (10))) (.branch 7 (.leaf (12)) (.leaf (13))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (15)) (.leaf (16))) (.branch 11 (.leaf (17)) (.leaf (18)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (7))) (.branch 15 (.leaf (9)) (.leaf (22)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (24)) (.leaf (26))) (.branch 19 (.leaf (28)) (.leaf (29)))) (.branch 22 (.branch 21 (.leaf (31)) (.leaf (32))) (.branch 23 (.leaf (34)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (35)) (.leaf (0))) (.branch 27 (.leaf (37)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (38)) (.leaf (40))) (.branch 31 (.leaf (41)) (.leaf (43))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (36)) (.leaf (45))) (.branch 35 (.leaf (47)) (.leaf (49)))) (.branch 38 (.branch 37 (.leaf (50)) (.leaf (52))) (.branch 39 (.leaf (54)) (.leaf (11))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (19)) (.leaf (56))) (.branch 43 (.leaf (57)) (.leaf (25)))) (.branch 46 (.branch 45 (.leaf (14)) (.leaf (59))) (.branch 47 (.leaf (55)) (.leaf (53)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (44)) (.leaf (62))) (.branch 51 (.leaf (63)) (.leaf (27)))) (.branch 54 (.branch 53 (.leaf (65)) (.leaf (23))) (.branch 55 (.leaf (67)) (.leaf (68))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (70)) (.leaf (66))) (.branch 59 (.leaf (21)) (.leaf (33)))) (.branch 62 (.branch 61 (.leaf (72)) (.leaf (73))) (.branch 63 (.leaf (48)) (.leaf (76)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (74)) (.leaf (51))) (.branch 67 (.leaf (42)) (.leaf (78)))) (.branch 70 (.branch 69 (.leaf (79)) (.leaf (58))) (.branch 71 (.leaf (81)) (.leaf (30))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (75)) (.leaf (83))) (.branch 75 (.leaf (84)) (.leaf (60)))) (.branch 78 (.branch 77 (.leaf (69)) (.leaf (82))) (.branch 79 (.leaf (39)) (.leaf (87)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (77)) (.leaf (89))) (.branch 83 (.leaf (46)) (.leaf (91)))) (.branch 86 (.branch 85 (.leaf (93)) (.leaf (71))) (.branch 87 (.leaf (85)) (.leaf (95))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (96)) (.leaf (86))) (.branch 91 (.leaf (64)) (.leaf (98)))) (.branch 94 (.branch 93 (.leaf (61)) (.leaf (100))) (.branch 95 (.leaf (101)) (.leaf (80))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (102)) (.leaf (103))) (.branch 99 (.leaf (105)) (.leaf (106)))) (.branch 102 (.branch 101 (.leaf (108)) (.leaf (109))) (.branch 103 (.leaf (110)) (.leaf (112))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (113)) (.leaf (115))) (.branch 107 (.leaf (117)) (.leaf (118)))) (.branch 110 (.branch 109 (.leaf (120)) (.leaf (121))) (.branch 111 (.leaf (88)) (.leaf (90)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (97)) (.leaf (122))) (.branch 115 (.leaf (123)) (.leaf (116)))) (.branch 118 (.branch 117 (.leaf (92)) (.leaf (99))) (.branch 119 (.leaf (124)) (.leaf (125))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (111)) (.leaf (94))) (.branch 123 (.leaf (126)) (.leaf (114)))) (.branch 126 (.branch 125 (.leaf (127)) (.leaf (119))) (.branch 127 (.leaf (104)) (.leaf (107)))))))))
noncomputable def originalT (p : Fin 128) : Fin 128 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 64) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (3))) (.branch 15 (.leaf (4)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (9)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 21 (.leaf (12)) (.leaf (7))) (.branch 23 (.leaf (8)) (.leaf (13))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (14)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))) (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 31 (.leaf (18)) (.leaf (19))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.leaf (20)))) (.branch 38 (.branch 37 (.leaf (16)) (.leaf (20))) (.branch 39 (.leaf (21)) (.leaf (22))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (23)) (.leaf (24))) (.branch 43 (.leaf (25)) (.leaf (26)))) (.branch 46 (.branch 45 (.leaf (15)) (.leaf (17))) (.branch 47 (.leaf (18)) (.leaf (19)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (27)) (.leaf (28))) (.branch 51 (.leaf (21)) (.leaf (27)))) (.branch 54 (.branch 53 (.leaf (28)) (.leaf (26))) (.branch 55 (.leaf (29)) (.leaf (24))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (30)) (.leaf (31))) (.branch 59 (.leaf (22)) (.leaf (23)))) (.branch 62 (.branch 61 (.leaf (25)) (.leaf (32))) (.branch 63 (.leaf (33)) (.leaf (29)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (32)) (.leaf (33))) (.branch 67 (.leaf (34)) (.leaf (35)))) (.branch 70 (.branch 69 (.leaf (30)) (.leaf (36))) (.branch 71 (.leaf (37)) (.leaf (38))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (31)) (.leaf (39))) (.branch 75 (.leaf (39)) (.leaf (34)))) (.branch 78 (.branch 77 (.leaf (35)) (.leaf (40))) (.branch 79 (.leaf (36)) (.leaf (37)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (41)) (.leaf (42))) (.branch 83 (.leaf (38)) (.leaf (43)))) (.branch 86 (.branch 85 (.leaf (43)) (.leaf (40))) (.branch 87 (.leaf (41)) (.leaf (42))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (44)) (.leaf (45))) (.branch 91 (.leaf (46)) (.leaf (47)))) (.branch 94 (.branch 93 (.leaf (46)) (.leaf (47))) (.branch 95 (.leaf (44)) (.leaf (45))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (48)) (.leaf (49))) (.branch 99 (.leaf (50)) (.leaf (49)))) (.branch 102 (.branch 101 (.leaf (50)) (.leaf (48))) (.branch 103 (.leaf (51)) (.leaf (52))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (53)) (.leaf (54))) (.branch 107 (.leaf (52)) (.leaf (53)))) (.branch 110 (.branch 109 (.leaf (54)) (.leaf (51))) (.branch 111 (.leaf (55)) (.leaf (56)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (57)) (.leaf (58))) (.branch 115 (.leaf (59)) (.leaf (60)))) (.branch 118 (.branch 117 (.leaf (56)) (.leaf (57))) (.branch 119 (.leaf (58)) (.leaf (59))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (60)) (.leaf (55))) (.branch 123 (.leaf (61)) (.leaf (62)))) (.branch 126 (.branch 125 (.leaf (61)) (.leaf (62))) (.branch 127 (.leaf (63)) (.leaf (63)))))))))
noncomputable def projection (p : Fin 128) : Fin 64 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 128) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (6))) (.branch 7 (.leaf (9)) (.leaf (11))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (16))) (.branch 11 (.leaf (18)) (.leaf (19)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (23))) (.branch 15 (.leaf (24)) (.leaf (27)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (28)) (.leaf (29))) (.branch 19 (.leaf (30)) (.leaf (31)))) (.branch 22 (.branch 21 (.leaf (35)) (.leaf (38))) (.branch 23 (.leaf (39)) (.leaf (40))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (41)) (.leaf (42))) (.branch 27 (.leaf (43)) (.leaf (48)))) (.branch 30 (.branch 29 (.leaf (49)) (.leaf (54))) (.branch 31 (.leaf (56)) (.leaf (57))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (61)) (.leaf (62))) (.branch 35 (.leaf (66)) (.leaf (67)))) (.branch 38 (.branch 37 (.leaf (69)) (.leaf (70))) (.branch 39 (.leaf (71)) (.leaf (73))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (77)) (.leaf (80))) (.branch 43 (.leaf (81)) (.leaf (83)))) (.branch 46 (.branch 45 (.leaf (88)) (.leaf (89))) (.branch 47 (.leaf (90)) (.leaf (91)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (96)) (.leaf (97))) (.branch 51 (.leaf (98)) (.leaf (102)))) (.branch 54 (.branch 53 (.leaf (103)) (.leaf (104))) (.branch 55 (.leaf (105)) (.leaf (110))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (111)) (.leaf (112))) (.branch 59 (.leaf (113)) (.leaf (114)))) (.branch 62 (.branch 61 (.leaf (115)) (.leaf (122))) (.branch 63 (.leaf (123)) (.leaf (126))))))))
noncomputable def representative (p : Fin 64) : Fin 128 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (7))) (.branch 7 (.leaf (3)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (11)) (.leaf (13))) (.branch 11 (.leaf (15)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (18)) (.leaf (9))) (.branch 15 (.leaf (16)) (.leaf (10)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (22))) (.branch 19 (.leaf (12)) (.leaf (25)))) (.branch 22 (.branch 21 (.leaf (27)) (.leaf (26))) (.branch 23 (.leaf (17)) (.leaf (24))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (23)) (.leaf (19))) (.branch 27 (.leaf (21)) (.leaf (20)))) (.branch 30 (.branch 29 (.leaf (32)) (.leaf (34))) (.branch 31 (.leaf (36)) (.leaf (38))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (28)) (.leaf (39))) (.branch 35 (.leaf (29)) (.leaf (40)))) (.branch 38 (.branch 37 (.leaf (30)) (.leaf (41))) (.branch 39 (.leaf (31)) (.leaf (33))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (35)) (.leaf (37))) (.branch 43 (.leaf (44)) (.leaf (46)))) (.branch 46 (.branch 45 (.leaf (42)) (.leaf (48))) (.branch 47 (.leaf (43)) (.leaf (49)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (45)) (.leaf (47))) (.branch 51 (.leaf (53)) (.leaf (55)))) (.branch 54 (.branch 53 (.leaf (56)) (.leaf (50))) (.branch 55 (.leaf (59)) (.leaf (51))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (52)) (.leaf (58))) (.branch 59 (.leaf (57)) (.leaf (54)))) (.branch 62 (.branch 61 (.leaf (61)) (.leaf (60))) (.branch 63 (.leaf (63)) (.leaf (62))))))))
noncomputable def S (p : Fin 64) : Fin 64 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (8))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (14))) (.branch 11 (.leaf (16)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (19)) (.leaf (0))) (.branch 15 (.leaf (20)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (21)) (.leaf (23))) (.branch 19 (.leaf (24)) (.leaf (26)))) (.branch 22 (.branch 21 (.leaf (28)) (.leaf (29))) (.branch 23 (.leaf (7)) (.leaf (11))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (30)) (.leaf (31))) (.branch 27 (.leaf (13)) (.leaf (15)))) (.branch 30 (.branch 29 (.leaf (33)) (.leaf (35))) (.branch 31 (.leaf (37)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (39)) (.leaf (27))) (.branch 35 (.leaf (25)) (.leaf (36)))) (.branch 38 (.branch 37 (.leaf (22)) (.leaf (42))) (.branch 39 (.leaf (18)) (.leaf (43))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (38)) (.leaf (40))) (.branch 43 (.leaf (45)) (.leaf (47)))) (.branch 46 (.branch 45 (.leaf (48)) (.leaf (41))) (.branch 47 (.leaf (32)) (.leaf (50)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (51)) (.leaf (52))) (.branch 51 (.leaf (54)) (.leaf (55)))) (.branch 54 (.branch 53 (.leaf (57)) (.leaf (58))) (.branch 55 (.leaf (60)) (.leaf (44))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (46)) (.leaf (49))) (.branch 59 (.leaf (61)) (.leaf (62)))) (.branch 62 (.branch 61 (.leaf (56)) (.leaf (63))) (.branch 63 (.leaf (59)) (.leaf (53))))))))
noncomputable def T (p : Fin 64) : Fin 64 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (13)) (.leaf (3))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (15)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (22))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (23)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (26))) (.branch 15 (.leaf (9)) (.leaf (27)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (38)) (.leaf (12)))) (.branch 22 (.branch 21 (.leaf (14)) (.leaf (16))) (.branch 23 (.leaf (36)) (.leaf (17))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (18)) (.leaf (34))) (.branch 27 (.leaf (19)) (.leaf (33)))) (.branch 30 (.branch 29 (.leaf (20)) (.leaf (21))) (.branch 31 (.leaf (24)) (.leaf (25))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (46)) (.leaf (28))) (.branch 35 (.leaf (31)) (.leaf (29)))) (.branch 38 (.branch 37 (.leaf (35)) (.leaf (30))) (.branch 39 (.leaf (40)) (.leaf (32))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (41)) (.leaf (45))) (.branch 43 (.leaf (37)) (.leaf (39)))) (.branch 46 (.branch 45 (.leaf (55)) (.leaf (42))) (.branch 47 (.leaf (56)) (.leaf (43)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (44)) (.leaf (57))) (.branch 51 (.leaf (47)) (.leaf (48)))) (.branch 54 (.branch 53 (.leaf (49)) (.leaf (63))) (.branch 55 (.leaf (50)) (.leaf (51))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (60)) (.leaf (52))) (.branch 59 (.leaf (53)) (.leaf (62)))) (.branch 62 (.branch 61 (.leaf (54)) (.leaf (58))) (.branch 63 (.leaf (59)) (.leaf (61))))))))
noncomputable def Ti (p : Fin 64) : Fin 64 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 64) : Fin 64 := T (S p)
theorem quotient_relations : (∀ p : Fin 64, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 128, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 128, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 64, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 64)) := [[0,3,9],[1,2,6],[4,5,10],[7,8,17],[11,12,24],[13,14,21],[15,16,20],[18,19,31],[22,23,30],[25,26,29],[27,28,39],[32,33,43],[34,35,38],[36,37,40],[41,42,48],[44,45,51],[46,47,52],[49,50,58],[53,54,62],[55],[56,57,61],[59,60,63]]
noncomputable def verticesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (5)) (.leaf (9))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (2))) (.branch 11 (.leaf (8)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (13)) (.leaf (15))) (.branch 15 (.leaf (16)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (19)) (.leaf (11))) (.branch 19 (.leaf (21)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (20)) (.leaf (17))) (.branch 23 (.leaf (24)) (.leaf (25))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (14)) (.leaf (27))) (.branch 27 (.leaf (28)) (.leaf (30)))) (.branch 30 (.branch 29 (.leaf (31)) (.leaf (29))) (.branch 31 (.leaf (26)) (.leaf (23))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (33)) (.leaf (34))) (.branch 35 (.leaf (36)) (.leaf (37)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (40))) (.branch 39 (.leaf (38)) (.leaf (32))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (41)) (.leaf (42))) (.branch 43 (.leaf (43)) (.leaf (35)))) (.branch 46 (.branch 45 (.leaf (45)) (.leaf (46))) (.branch 47 (.leaf (48)) (.leaf (49)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (44)) (.leaf (51))) (.branch 51 (.leaf (52)) (.leaf (47)))) (.branch 54 (.branch 53 (.leaf (50)) (.leaf (54))) (.branch 55 (.leaf (55)) (.leaf (57))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (58)) (.leaf (59))) (.branch 59 (.leaf (53)) (.leaf (61)))) (.branch 62 (.branch 61 (.leaf (62)) (.leaf (60))) (.branch 63 (.leaf (56)) (.leaf (63))))))))
noncomputable def verticesIndex (p : Fin 64) : Fin 64 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (9)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (7))) (.branch 11 (.leaf (8)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (12))) (.branch 15 (.leaf (24)) (.leaf (13)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (21))) (.branch 19 (.leaf (15)) (.leaf (16)))) (.branch 22 (.branch 21 (.leaf (20)) (.leaf (18))) (.branch 23 (.leaf (19)) (.leaf (31))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (22)) (.leaf (23))) (.branch 27 (.leaf (30)) (.leaf (25)))) (.branch 30 (.branch 29 (.leaf (26)) (.leaf (29))) (.branch 31 (.leaf (27)) (.leaf (28))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (39)) (.leaf (32))) (.branch 35 (.leaf (33)) (.leaf (43)))) (.branch 38 (.branch 37 (.leaf (34)) (.leaf (35))) (.branch 39 (.leaf (38)) (.leaf (36))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (40))) (.branch 43 (.leaf (41)) (.leaf (42)))) (.branch 46 (.branch 45 (.leaf (48)) (.leaf (44))) (.branch 47 (.leaf (45)) (.leaf (51)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (46)) (.leaf (47))) (.branch 51 (.leaf (52)) (.leaf (49)))) (.branch 54 (.branch 53 (.leaf (50)) (.leaf (58))) (.branch 55 (.leaf (53)) (.leaf (54))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (62)) (.leaf (55))) (.branch 59 (.leaf (56)) (.leaf (57)))) (.branch 62 (.branch 61 (.leaf (61)) (.leaf (59))) (.branch 63 (.leaf (60)) (.leaf (63))))))))
noncomputable def verticesBack (p : Fin 64) : Fin 64 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 64, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 64 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 64, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 64)) := [[0,1],[2,4],[3,6],[5,7],[8,11],[9,13],[10,15],[12,18],[14,16],[17,22],[19,25],[20,27],[21,26],[23,24],[28,32],[29,34],[30,36],[31,38],[33,39],[35,40],[37,41],[42,44],[43,46],[45,48],[47,49],[50,53],[51,55],[52,56],[54,59],[57,58],[60,61],[62,63]]
noncomputable def edgesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (8)) (.leaf (10))) (.branch 11 (.leaf (12)) (.leaf (9)))) (.branch 14 (.branch 13 (.leaf (14)) (.leaf (11))) (.branch 15 (.leaf (16)) (.leaf (13)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (17)) (.leaf (18))) (.branch 19 (.leaf (15)) (.leaf (20)))) (.branch 22 (.branch 21 (.leaf (22)) (.leaf (24))) (.branch 23 (.leaf (19)) (.leaf (26))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (27)) (.leaf (21))) (.branch 27 (.leaf (25)) (.leaf (23)))) (.branch 30 (.branch 29 (.leaf (28)) (.leaf (30))) (.branch 31 (.leaf (32)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (29)) (.leaf (36))) (.branch 35 (.leaf (31)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (40))) (.branch 39 (.leaf (35)) (.leaf (37))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (39)) (.leaf (41))) (.branch 43 (.leaf (42)) (.leaf (44)))) (.branch 46 (.branch 45 (.leaf (43)) (.leaf (46))) (.branch 47 (.leaf (45)) (.leaf (48)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (47)) (.leaf (49))) (.branch 51 (.leaf (50)) (.leaf (52)))) (.branch 54 (.branch 53 (.leaf (54)) (.leaf (51))) (.branch 55 (.leaf (56)) (.leaf (53))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (55)) (.leaf (58))) (.branch 59 (.leaf (59)) (.leaf (57)))) (.branch 62 (.branch 61 (.leaf (60)) (.leaf (61))) (.branch 63 (.leaf (62)) (.leaf (63))))))))
noncomputable def edgesIndex (p : Fin 64) : Fin 64 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (8)) (.leaf (11))) (.branch 11 (.leaf (9)) (.leaf (13)))) (.branch 14 (.branch 13 (.leaf (10)) (.leaf (15))) (.branch 15 (.leaf (12)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (16))) (.branch 19 (.leaf (17)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (25))) (.branch 23 (.leaf (20)) (.leaf (27))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (26))) (.branch 27 (.leaf (23)) (.leaf (24)))) (.branch 30 (.branch 29 (.leaf (28)) (.leaf (32))) (.branch 31 (.leaf (29)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (30)) (.leaf (36))) (.branch 35 (.leaf (31)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (39))) (.branch 39 (.leaf (35)) (.leaf (40))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (41))) (.branch 43 (.leaf (42)) (.leaf (44)))) (.branch 46 (.branch 45 (.leaf (43)) (.leaf (46))) (.branch 47 (.leaf (45)) (.leaf (48)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (47)) (.leaf (49))) (.branch 51 (.leaf (50)) (.leaf (53)))) (.branch 54 (.branch 53 (.leaf (51)) (.leaf (55))) (.branch 55 (.leaf (52)) (.leaf (56))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (54)) (.leaf (59))) (.branch 59 (.leaf (57)) (.leaf (58)))) (.branch 62 (.branch 61 (.leaf (60)) (.leaf (61))) (.branch 63 (.leaf (62)) (.leaf (63))))))))
noncomputable def edgesBack (p : Fin 64) : Fin 64 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 64, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 64 := by decide +kernel
theorem edges_partition : ∀ p : Fin 64, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 64)) := [[0,2,5,8,12,19,26,13],[1,3],[4,6,9,14,20,28,33,27,15],[7,10,16,21,29,35,36,22],[11,17,23],[18,24,30,37,42,45,41,40,38],[25,31,34],[32,39,43,47,50,54,60,56,46],[44,48,51,55],[49,52,57],[53,58,61,63],[59,62]]
noncomputable def facesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (8))) (.branch 3 (.leaf (1)) (.leaf (9)))) (.branch 6 (.branch 5 (.leaf (10)) (.leaf (2))) (.branch 7 (.leaf (11)) (.leaf (19))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (12))) (.branch 11 (.leaf (20)) (.leaf (27)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (7))) (.branch 15 (.leaf (13)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (21)) (.leaf (28))) (.branch 19 (.leaf (30)) (.leaf (5)))) (.branch 22 (.branch 21 (.leaf (14)) (.leaf (22))) (.branch 23 (.leaf (26)) (.leaf (29))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (31)) (.leaf (39))) (.branch 27 (.leaf (6)) (.leaf (17)))) (.branch 30 (.branch 29 (.leaf (15)) (.leaf (23))) (.branch 31 (.leaf (32)) (.leaf (40))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (42)) (.leaf (16))) (.branch 35 (.leaf (41)) (.leaf (24)))) (.branch 38 (.branch 37 (.leaf (25)) (.leaf (33))) (.branch 39 (.leaf (38)) (.leaf (43))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (36))) (.branch 43 (.leaf (34)) (.leaf (44)))) (.branch 46 (.branch 45 (.leaf (51)) (.leaf (35))) (.branch 47 (.leaf (50)) (.leaf (45)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (52)) (.leaf (55))) (.branch 51 (.leaf (46)) (.leaf (53)))) (.branch 54 (.branch 53 (.leaf (56)) (.leaf (58))) (.branch 55 (.leaf (47)) (.leaf (54))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (49)) (.leaf (57))) (.branch 59 (.leaf (59)) (.leaf (62)))) (.branch 62 (.branch 61 (.leaf (48)) (.leaf (60))) (.branch 63 (.leaf (63)) (.leaf (61))))))))
noncomputable def facesIndex (p : Fin 64) : Fin 64 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (12)) (.leaf (19))) (.branch 7 (.leaf (26)) (.leaf (13))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (1)) (.leaf (3))) (.branch 11 (.leaf (4)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (9)) (.leaf (14))) (.branch 15 (.leaf (20)) (.leaf (28)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (33)) (.leaf (27))) (.branch 19 (.leaf (15)) (.leaf (7)))) (.branch 22 (.branch 21 (.leaf (10)) (.leaf (16))) (.branch 23 (.leaf (21)) (.leaf (29))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (35)) (.leaf (36))) (.branch 27 (.leaf (22)) (.leaf (11)))) (.branch 30 (.branch 29 (.leaf (17)) (.leaf (23))) (.branch 31 (.leaf (18)) (.leaf (24))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (30)) (.leaf (37))) (.branch 35 (.leaf (42)) (.leaf (45)))) (.branch 38 (.branch 37 (.leaf (41)) (.leaf (40))) (.branch 39 (.leaf (38)) (.leaf (25))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (31)) (.leaf (34))) (.branch 43 (.leaf (32)) (.leaf (39)))) (.branch 46 (.branch 45 (.leaf (43)) (.leaf (47))) (.branch 47 (.leaf (50)) (.leaf (54)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (60)) (.leaf (56))) (.branch 51 (.leaf (46)) (.leaf (44)))) (.branch 54 (.branch 53 (.leaf (48)) (.leaf (51))) (.branch 55 (.leaf (55)) (.leaf (49))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (52)) (.leaf (57))) (.branch 59 (.leaf (53)) (.leaf (58)))) (.branch 62 (.branch 61 (.leaf (61)) (.leaf (63))) (.branch 63 (.leaf (59)) (.leaf (62))))))))
noncomputable def facesBack (p : Fin 64) : Fin 64 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 64, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 64 := by decide +kernel
theorem faces_partition : ∀ p : Fin 64, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [8,2,9,8,3,9,3,9,4,3,4,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 22 - 32 + 12 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 1 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨2,-1,1,0⟩))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (⟨-1,-3,0,-1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 11 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨-3,1,-1,0⟩)))) (.branch 14 (.branch 13 (.leaf (⟨1,4,0,1⟩)) (.leaf (⟨-1,-7,0,-1⟩))) (.branch 15 (.leaf (⟨-7,-6,-1,-1⟩)) (.leaf (⟨1,-2,1,-1⟩)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (⟨-2,-3,-1,-2⟩)) (.leaf (⟨-3,-2,-1,-1⟩))) (.branch 19 (.leaf (⟨4,-1,1,0⟩)) (.leaf (⟨-1,-5,0,-1⟩)))) (.branch 22 (.branch 21 (.leaf (⟨-3,-1,-2,-1⟩)) (.leaf (⟨6,-1,1,0⟩))) (.branch 23 (.leaf (⟨-2,3,-1,1⟩)) (.leaf (⟨3,5,1,2⟩))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (⟨4,3,1,1⟩)) (.leaf (⟨-5,1,-1,0⟩))) (.branch 27 (.leaf (⟨1,6,0,1⟩)) (.leaf (⟨-1,3,-1,2⟩)))) (.branch 30 (.branch 29 (.leaf (⟨3,4,2,3⟩)) (.leaf (⟨6,5,1,1⟩))) (.branch 31 (.leaf (⟨5,2,2,1⟩)) (.leaf (⟨-5,-4,-1,-1⟩))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (⟨4,-3,3,-2⟩)) (.leaf (⟨-3,-7,-2,-5⟩))) (.branch 35 (.leaf (⟨5,9,1,2⟩)) (.leaf (⟨9,4,2,1⟩)))) (.branch 38 (.branch 37 (.leaf (⟨2,-5,1,-2⟩)) (.leaf (⟨-5,-7,-2,-3⟩))) (.branch 39 (.leaf (⟨-4,5,-1,1⟩)) (.leaf (⟨4,1,3,1⟩))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (⟨-7,-2,-3,-1⟩)) (.leaf (⟨-7,5,-3,2⟩))) (.branch 43 (.leaf (⟨5,12,2,5⟩)) (.leaf (⟨-7,-4,-5,-3⟩)))) (.branch 46 (.branch 45 (.leaf (⟨12,-5,5,-2⟩)) (.leaf (⟨-5,-17,-2,-7⟩))) (.branch 47 (.leaf (⟨-4,7,-3,5⟩)) (.leaf (⟨7,11,5,8⟩)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (⟨12,7,5,3⟩)) (.leaf (⟨11,-7,8,-5⟩))) (.branch 51 (.leaf (⟨-7,-18,-5,-13⟩)) (.leaf (⟨-17,-12,-7,-5⟩)))) (.branch 54 (.branch 53 (.leaf (⟨11,4,8,3⟩)) (.leaf (⟨-18,7,-13,5⟩))) (.branch 55 (.leaf (⟨7,25,5,18⟩)) (.leaf (⟨-12,17,-5,7⟩))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (⟨4,-11,3,-8⟩)) (.leaf (⟨-11,-15,-8,-11⟩))) (.branch 59 (.leaf (⟨-18,-11,-13,-8⟩)) (.leaf (⟨19,4,14,3⟩)))) (.branch 62 (.branch 61 (.leaf (⟨-4,15,-3,11⟩)) (.leaf (⟨-15,-4,-11,-3⟩))) (.branch 63 (.leaf (⟨25,18,18,13⟩)) (.leaf (⟨15,19,11,14⟩))))))))
noncomputable def liftMatrix (p : Fin 64) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 64) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],6⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],7⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],10⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],11⟩,⟨⟨1,4,0,1⟩,[.t (4)],12⟩,⟨⟨-1,-7,0,-1⟩,[.t (7)],13⟩,⟨⟨-7,-6,-1,-1⟩,[.t (7),.s,.t (1)],14⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],15⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],16⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],17⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],18⟩,⟨⟨-1,-5,0,-1⟩,[.t (5)],19⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],20⟩,⟨⟨6,-1,1,0⟩,[.t (6),.s,.t (0)],21⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],22⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],23⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],24⟩,⟨⟨-5,1,-1,0⟩,[.t (5),.s,.t (0)],25⟩,⟨⟨1,6,0,1⟩,[.t (6)],26⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],27⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],28⟩,⟨⟨6,5,1,1⟩,[.t (6),.s,.t (1)],29⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],30⟩,⟨⟨-5,-4,-1,-1⟩,[.t (5),.s,.t (1)],31⟩,⟨⟨4,-3,3,-2⟩,[.t (1),.s,.t (-3),.s,.t (-1)],32⟩,⟨⟨-3,-7,-2,-5⟩,[.t (1),.s,.t (-2),.s,.t (2)],33⟩,⟨⟨5,9,1,2⟩,[.t (5),.s,.t (2)],34⟩,⟨⟨9,4,2,1⟩,[.t (4),.s,.t (-2),.s,.t (0)],35⟩,⟨⟨2,-5,1,-2⟩,[.t (2),.s,.t (-2)],36⟩,⟨⟨-5,-7,-2,-3⟩,[.t (2),.s,.t (-2),.s,.t (1)],37⟩,⟨⟨-4,5,-1,1⟩,[.t (4),.s,.t (-1)],38⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],39⟩,⟨⟨-7,-2,-3,-1⟩,[.t (2),.s,.t (-3),.s,.t (0)],40⟩,⟨⟨-7,5,-3,2⟩,[.t (2),.s,.t (-3),.s,.t (-1)],41⟩,⟨⟨5,12,2,5⟩,[.t (2),.s,.t (-2),.s,.t (2)],42⟩,⟨⟨-7,-4,-5,-3⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (0)],43⟩,⟨⟨12,-5,5,-2⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],44⟩,⟨⟨-5,-17,-2,-7⟩,[.t (2),.s,.t (-2),.s,.t (3)],45⟩,⟨⟨-4,7,-3,5⟩,[.t (1),.s,.t (-3),.s,.t (-2)],46⟩,⟨⟨7,11,5,8⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (1)],47⟩,⟨⟨12,7,5,3⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (0)],48⟩,⟨⟨11,-7,8,-5⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-1)],49⟩,⟨⟨-7,-18,-5,-13⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (2)],50⟩,⟨⟨-17,-12,-7,-5⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],51⟩,⟨⟨11,4,8,3⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (0)],52⟩,⟨⟨-18,7,-13,5⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-1)],53⟩,⟨⟨7,25,5,18⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (3)],54⟩,⟨⟨-12,17,-5,7⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],55⟩,⟨⟨4,-11,3,-8⟩,[.t (1),.s,.t (-3),.s,.t (-3)],56⟩,⟨⟨-11,-15,-8,-11⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (1)],57⟩,⟨⟨-18,-11,-13,-8⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (0)],58⟩,⟨⟨19,4,14,3⟩,[.t (1),.s,.t (-3),.s,.t (-5),.s,.t (0)],59⟩,⟨⟨-4,15,-3,11⟩,[.t (1),.s,.t (-3),.s,.t (-4)],60⟩,⟨⟨-15,-4,-11,-3⟩,[.t (1),.s,.t (-3),.s,.t (-4),.s,.t (0)],61⟩,⟨⟨25,18,18,13⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],62⟩,⟨⟨15,19,11,14⟩,[.t (1),.s,.t (-3),.s,.t (-4),.s,.t (1)],63⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 64 ∧ ((List.finRange 64).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 64) := [⟨9,2,⟨⟨-1,-8,0,-1⟩,[.t (8)],0⟩⟩,⟨3,1,⟨⟨-1,0,-2,-1⟩,[.t (0),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨6,1,⟨⟨-1,0,2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨39,6,⟨⟨16,-19,11,-13⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨59,9,⟨⟨-173,233,-124,167⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨63,11,⟨⟨-527,717,-380,517⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨57,10,⟨⟨265,-363,192,-263⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨58,10,⟨⟨-263,363,-192,265⟩,[.t (1),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨62,11,⟨⟨517,-717,380,-527⟩,[.t (1),.s,.t (-3),.s,.t (-5),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨54,9,⟨⟨167,-233,124,-173⟩,[.t (1),.s,.t (-3),.s,.t (-9),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨33,6,⟨⟨-13,19,-11,16⟩,[.t (1),.s,.t (-6),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨16,3,⟨⟨-19,32,-3,5⟩,[.t (6),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨40,7,⟨⟨31,-71,7,-16⟩,[.t (4),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨48,8,⟨⟨76,-179,31,-73⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨55,-3,⟨⟨264,-637,109,-263⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨45,8,⟨⟨-73,179,-31,76⟩,[.t (2),.s,.t (-3),.s,.t (-6),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨23,4,⟨⟨10,-27,3,-8⟩,[.t (3),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨24,4,⟨⟨-8,27,-3,10⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨35,7,⟨⟨-16,71,-7,31⟩,[.t (2),.s,.t (-4),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨34,5,⟨⟨-16,75,-3,14⟩,[.t (5),.s,.t (-3),.s,.t (-5)],0⟩⟩,⟨29,5,⟨⟨14,-75,3,-16⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (-6)],0⟩⟩,⟨14,3,⟨⟨5,-32,3,-19⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-7)],0⟩⟩,⟨13,2,⟨⟨-1,8,0,-1⟩,[.t (-8)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(0,1),(1,1),(4,3),(19,14),(15,11),(11,8),(18,13),(25,18),(7,5),(3,2),(2,1),(7,3),(12,5),(17,7),(5,2),(3,1),(4,1),(9,2),(5,1),(6,1),(7,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end PSL2_17_c5

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
