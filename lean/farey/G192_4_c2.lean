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
namespace G192_4_c2
noncomputable def originalSData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (8))) (.branch 7 (.leaf (12)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (13))) (.branch 11 (.leaf (16)) (.leaf (18)))) (.branch 14 (.branch 13 (.leaf (15)) (.leaf (21))) (.branch 15 (.leaf (2)) (.leaf (24)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (22)) (.leaf (26))) (.branch 19 (.leaf (23)) (.leaf (28)))) (.branch 22 (.branch 21 (.leaf (29)) (.leaf (4))) (.branch 23 (.leaf (31)) (.leaf (33))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (36))) (.branch 27 (.leaf (32)) (.leaf (39)))) (.branch 30 (.branch 29 (.leaf (34)) (.leaf (35))) (.branch 31 (.leaf (42)) (.leaf (10))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (45)) (.leaf (11))) (.branch 35 (.leaf (47)) (.leaf (48)))) (.branch 38 (.branch 37 (.leaf (44)) (.leaf (50))) (.branch 39 (.leaf (51)) (.leaf (46))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (54)) (.leaf (55))) (.branch 43 (.leaf (49)) (.leaf (58)))) (.branch 46 (.branch 45 (.leaf (59)) (.leaf (17))) (.branch 47 (.leaf (62)) (.leaf (19)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (20)) (.leaf (65))) (.branch 51 (.leaf (60)) (.leaf (61)))) (.branch 54 (.branch 53 (.leaf (68)) (.leaf (37))) (.branch 55 (.leaf (63)) (.leaf (64))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (71)) (.leaf (73))) (.branch 59 (.leaf (66)) (.leaf (25)))) (.branch 62 (.branch 61 (.leaf (53)) (.leaf (76))) (.branch 63 (.leaf (27)) (.leaf (78)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (79)) (.leaf (30))) (.branch 67 (.leaf (67)) (.leaf (43)))) (.branch 70 (.branch 69 (.leaf (77)) (.leaf (84))) (.branch 71 (.leaf (86)) (.leaf (80))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (88)) (.leaf (81))) (.branch 75 (.leaf (90)) (.leaf (92)))) (.branch 78 (.branch 77 (.leaf (38)) (.leaf (93))) (.branch 79 (.leaf (40)) (.leaf (41)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (87)) (.leaf (97))) (.branch 83 (.leaf (99)) (.leaf (101)))) (.branch 86 (.branch 85 (.leaf (94)) (.leaf (103))) (.branch 87 (.leaf (95)) (.leaf (56))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (96)) (.leaf (105))) (.branch 91 (.leaf (98)) (.leaf (107)))) (.branch 94 (.branch 93 (.leaf (82)) (.leaf (52))) (.branch 95 (.leaf (110)) (.leaf (112))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (100)) (.leaf (57))) (.branch 99 (.leaf (114)) (.leaf (75)))) (.branch 102 (.branch 101 (.leaf (72)) (.leaf (109))) (.branch 103 (.leaf (89)) (.leaf (111))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (117)) (.leaf (113))) (.branch 107 (.leaf (83)) (.leaf (115)))) (.branch 110 (.branch 109 (.leaf (118)) (.leaf (106))) (.branch 111 (.leaf (69)) (.leaf (119)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (70)) (.leaf (102))) (.branch 115 (.leaf (74)) (.leaf (121)))) (.branch 118 (.branch 117 (.leaf (108)) (.leaf (120))) (.branch 119 (.leaf (122)) (.leaf (85))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (126)) (.leaf (91))) (.branch 123 (.leaf (116)) (.leaf (127)))) (.branch 126 (.branch 125 (.leaf (123)) (.leaf (124))) (.branch 127 (.leaf (104)) (.leaf (125)))))))))
noncomputable def originalS (p : Fin 128) : Fin 128 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (10)) (.leaf (11))) (.branch 7 (.leaf (0)) (.leaf (13))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (15)) (.leaf (12))) (.branch 11 (.leaf (17)) (.leaf (19)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (22))) (.branch 15 (.leaf (23)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (25)) (.leaf (27))) (.branch 19 (.leaf (1)) (.leaf (28)))) (.branch 22 (.branch 21 (.leaf (30)) (.leaf (24))) (.branch 23 (.leaf (32)) (.leaf (34))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (35)) (.leaf (37))) (.branch 27 (.leaf (38)) (.leaf (40)))) (.branch 30 (.branch 29 (.leaf (41)) (.leaf (5))) (.branch 31 (.leaf (43)) (.leaf (44))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (46)) (.leaf (7))) (.branch 35 (.leaf (47)) (.leaf (49)))) (.branch 38 (.branch 37 (.leaf (9)) (.leaf (26))) (.branch 39 (.leaf (52)) (.leaf (53))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (55)) (.leaf (56))) (.branch 43 (.leaf (57)) (.leaf (36)))) (.branch 46 (.branch 45 (.leaf (60)) (.leaf (61))) (.branch 47 (.leaf (63)) (.leaf (64)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (14)) (.leaf (66))) (.branch 51 (.leaf (67)) (.leaf (16)))) (.branch 54 (.branch 53 (.leaf (69)) (.leaf (58))) (.branch 55 (.leaf (70)) (.leaf (18))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (72)) (.leaf (74))) (.branch 59 (.leaf (75)) (.leaf (21)))) (.branch 62 (.branch 61 (.leaf (45)) (.leaf (77))) (.branch 63 (.leaf (50)) (.leaf (79)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (80)) (.leaf (81))) (.branch 67 (.leaf (59)) (.leaf (82)))) (.branch 70 (.branch 69 (.leaf (83)) (.leaf (85))) (.branch 71 (.leaf (87)) (.leaf (78))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (89)) (.leaf (29))) (.branch 75 (.leaf (91)) (.leaf (88)))) (.branch 78 (.branch 77 (.leaf (31)) (.leaf (94))) (.branch 79 (.leaf (95)) (.leaf (33)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (96)) (.leaf (98))) (.branch 83 (.leaf (100)) (.leaf (73)))) (.branch 86 (.branch 85 (.leaf (102)) (.leaf (104))) (.branch 87 (.leaf (39)) (.leaf (54))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (86)) (.leaf (68))) (.branch 91 (.leaf (106)) (.leaf (108)))) (.branch 94 (.branch 93 (.leaf (42)) (.leaf (109))) (.branch 95 (.leaf (111)) (.leaf (71))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (113)) (.leaf (48))) (.branch 99 (.leaf (115)) (.leaf (65)))) (.branch 102 (.branch 101 (.leaf (112)) (.leaf (51))) (.branch 103 (.leaf (92)) (.leaf (116))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (114)) (.leaf (99))) (.branch 107 (.leaf (76)) (.leaf (117)))) (.branch 110 (.branch 109 (.leaf (84)) (.leaf (97))) (.branch 111 (.leaf (105)) (.leaf (120)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (62)) (.leaf (93))) (.branch 115 (.leaf (101)) (.leaf (122)))) (.branch 118 (.branch 117 (.leaf (123)) (.leaf (124))) (.branch 119 (.leaf (125)) (.leaf (118))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (90)) (.leaf (126))) (.branch 123 (.leaf (110)) (.leaf (103)))) (.branch 126 (.branch 125 (.leaf (107)) (.leaf (119))) (.branch 127 (.leaf (127)) (.leaf (121)))))))))
noncomputable def originalT (p : Fin 128) : Fin 128 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 64) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (9)) (.leaf (3))) (.branch 15 (.leaf (4)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (12)) (.leaf (13)))) (.branch 22 (.branch 21 (.leaf (14)) (.leaf (6))) (.branch 23 (.leaf (7)) (.leaf (8))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (9)) (.leaf (15))) (.branch 27 (.leaf (16)) (.leaf (17)))) (.branch 30 (.branch 29 (.leaf (18)) (.leaf (19))) (.branch 31 (.leaf (20)) (.leaf (10))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (25)) (.leaf (26))) (.branch 43 (.leaf (27)) (.leaf (28)))) (.branch 46 (.branch 45 (.leaf (15)) (.leaf (16))) (.branch 47 (.leaf (17)) (.leaf (18)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (19)) (.leaf (20))) (.branch 51 (.leaf (29)) (.leaf (30)))) (.branch 54 (.branch 53 (.leaf (31)) (.leaf (29))) (.branch 55 (.leaf (32)) (.leaf (33))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (34)) (.leaf (35))) (.branch 59 (.leaf (36)) (.leaf (21)))) (.branch 62 (.branch 61 (.leaf (22)) (.leaf (23))) (.branch 63 (.leaf (24)) (.leaf (25)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (26)) (.leaf (27))) (.branch 67 (.leaf (28)) (.leaf (36)))) (.branch 70 (.branch 69 (.leaf (37)) (.leaf (38))) (.branch 71 (.leaf (39)) (.leaf (40))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (41)) (.leaf (42))) (.branch 75 (.leaf (43)) (.leaf (44)))) (.branch 78 (.branch 77 (.leaf (30)) (.leaf (31))) (.branch 79 (.leaf (32)) (.leaf (33)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (34)) (.leaf (35))) (.branch 83 (.leaf (44)) (.leaf (45)))) (.branch 86 (.branch 85 (.leaf (46)) (.leaf (47))) (.branch 87 (.leaf (48)) (.leaf (40))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (49)) (.leaf (50))) (.branch 91 (.leaf (51)) (.leaf (52)))) (.branch 94 (.branch 93 (.leaf (53)) (.leaf (37))) (.branch 95 (.leaf (38)) (.leaf (39))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (41)) (.leaf (42))) (.branch 99 (.leaf (43)) (.leaf (53)))) (.branch 102 (.branch 101 (.leaf (49)) (.leaf (54))) (.branch 103 (.leaf (55)) (.leaf (56))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (57)) (.leaf (55))) (.branch 107 (.leaf (54)) (.leaf (58)))) (.branch 110 (.branch 109 (.leaf (59)) (.leaf (45))) (.branch 111 (.leaf (46)) (.leaf (47)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (48)) (.leaf (50))) (.branch 115 (.leaf (51)) (.leaf (52)))) (.branch 118 (.branch 117 (.leaf (60)) (.leaf (61))) (.branch 119 (.leaf (60)) (.leaf (56))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (57)) (.leaf (58))) (.branch 123 (.leaf (59)) (.leaf (62)))) (.branch 126 (.branch 125 (.leaf (63)) (.leaf (62))) (.branch 127 (.leaf (61)) (.leaf (63)))))))))
noncomputable def projection (p : Fin 128) : Fin 64 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 128) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (6))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (11)) (.leaf (12))) (.branch 11 (.leaf (16)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (18)) (.leaf (19))) (.branch 15 (.leaf (20)) (.leaf (25)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (26)) (.leaf (27))) (.branch 19 (.leaf (28)) (.leaf (29)))) (.branch 22 (.branch 21 (.leaf (30)) (.leaf (36))) (.branch 23 (.leaf (37)) (.leaf (38))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (39)) (.leaf (40))) (.branch 27 (.leaf (41)) (.leaf (42)))) (.branch 30 (.branch 29 (.leaf (43)) (.leaf (50))) (.branch 31 (.leaf (51)) (.leaf (52))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (54)) (.leaf (55))) (.branch 35 (.leaf (56)) (.leaf (57)))) (.branch 38 (.branch 37 (.leaf (58)) (.leaf (68))) (.branch 39 (.leaf (69)) (.leaf (70))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (71)) (.leaf (72))) (.branch 43 (.leaf (73)) (.leaf (74)))) (.branch 46 (.branch 45 (.leaf (75)) (.leaf (83))) (.branch 47 (.leaf (84)) (.leaf (85)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (86)) (.leaf (88))) (.branch 51 (.leaf (89)) (.leaf (90)))) (.branch 54 (.branch 53 (.leaf (91)) (.leaf (92))) (.branch 55 (.leaf (101)) (.leaf (102))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (103)) (.leaf (104))) (.branch 59 (.leaf (107)) (.leaf (108)))) (.branch 62 (.branch 61 (.leaf (116)) (.leaf (117))) (.branch 63 (.leaf (123)) (.leaf (124))))))))
noncomputable def representative (p : Fin 64) : Fin 128 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (5))) (.branch 11 (.leaf (7)) (.leaf (16)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (18))) (.branch 15 (.leaf (19)) (.leaf (21)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (11)) (.leaf (24))) (.branch 19 (.leaf (13)) (.leaf (14)))) (.branch 22 (.branch 21 (.leaf (27)) (.leaf (15))) (.branch 23 (.leaf (29)) (.leaf (30))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (17)) (.leaf (32))) (.branch 27 (.leaf (33)) (.leaf (20)))) (.branch 30 (.branch 29 (.leaf (36)) (.leaf (22))) (.branch 31 (.leaf (23)) (.leaf (37))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (25)) (.leaf (26))) (.branch 35 (.leaf (40)) (.leaf (42)))) (.branch 38 (.branch 37 (.leaf (28)) (.leaf (31))) (.branch 39 (.leaf (46)) (.leaf (48))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (34)) (.leaf (49))) (.branch 43 (.leaf (35)) (.leaf (51)))) (.branch 46 (.branch 45 (.leaf (53)) (.leaf (54))) (.branch 47 (.leaf (38)) (.leaf (56)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (39)) (.leaf (41))) (.branch 51 (.leaf (55)) (.leaf (43)))) (.branch 54 (.branch 53 (.leaf (58)) (.leaf (44))) (.branch 55 (.leaf (45)) (.leaf (50))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (47)) (.leaf (61))) (.branch 59 (.leaf (52)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (57))) (.branch 63 (.leaf (63)) (.leaf (62))))))))
noncomputable def S (p : Fin 64) : Fin 64 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (9)) (.leaf (11))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (13)) (.leaf (14))) (.branch 11 (.leaf (15)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (18))) (.branch 15 (.leaf (20)) (.leaf (22)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (23)) (.leaf (25))) (.branch 19 (.leaf (26)) (.leaf (4)))) (.branch 22 (.branch 21 (.leaf (28)) (.leaf (6))) (.branch 23 (.leaf (16)) (.leaf (31))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (29)) (.leaf (33))) (.branch 27 (.leaf (34)) (.leaf (35)))) (.branch 30 (.branch 29 (.leaf (21)) (.leaf (36))) (.branch 31 (.leaf (10)) (.leaf (38))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (39)) (.leaf (12))) (.branch 35 (.leaf (41)) (.leaf (43)))) (.branch 38 (.branch 37 (.leaf (44)) (.leaf (45))) (.branch 39 (.leaf (47)) (.leaf (40))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (32)) (.leaf (50))) (.branch 43 (.leaf (19)) (.leaf (52)))) (.branch 46 (.branch 45 (.leaf (49)) (.leaf (42))) (.branch 47 (.leaf (55)) (.leaf (57)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (24)) (.leaf (48))) (.branch 51 (.leaf (37)) (.leaf (54)))) (.branch 54 (.branch 53 (.leaf (59)) (.leaf (27))) (.branch 55 (.leaf (30)) (.leaf (53))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (60)) (.leaf (51))) (.branch 59 (.leaf (61)) (.leaf (46)))) (.branch 62 (.branch 61 (.leaf (62)) (.leaf (63))) (.branch 63 (.leaf (56)) (.leaf (58))))))))
noncomputable def T (p : Fin 64) : Fin 64 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (5)) (.leaf (12))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (19)) (.leaf (2))) (.branch 7 (.leaf (21)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (6))) (.branch 11 (.leaf (30)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (33)) (.leaf (8))) (.branch 15 (.leaf (9)) (.leaf (10)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (22)) (.leaf (11))) (.branch 19 (.leaf (13)) (.leaf (42)))) (.branch 22 (.branch 21 (.leaf (14)) (.leaf (28))) (.branch 23 (.leaf (15)) (.leaf (16))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (48)) (.leaf (17))) (.branch 27 (.leaf (18)) (.leaf (53)))) (.branch 30 (.branch 29 (.leaf (20)) (.leaf (24))) (.branch 31 (.leaf (54)) (.leaf (23))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (40)) (.leaf (25))) (.branch 35 (.leaf (26)) (.leaf (27)))) (.branch 38 (.branch 37 (.leaf (29)) (.leaf (50))) (.branch 39 (.leaf (31)) (.leaf (32))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (39)) (.leaf (34))) (.branch 43 (.leaf (45)) (.leaf (35)))) (.branch 46 (.branch 45 (.leaf (36)) (.leaf (37))) (.branch 47 (.leaf (59)) (.leaf (38)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (49)) (.leaf (44))) (.branch 51 (.leaf (41)) (.leaf (57)))) (.branch 54 (.branch 53 (.leaf (43)) (.leaf (55))) (.branch 55 (.leaf (51)) (.leaf (46))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (62)) (.leaf (47))) (.branch 59 (.leaf (63)) (.leaf (52)))) (.branch 62 (.branch 61 (.leaf (56)) (.leaf (58))) (.branch 63 (.leaf (60)) (.leaf (61))))))))
noncomputable def Ti (p : Fin 64) : Fin 64 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 64) : Fin 64 := T (S p)
theorem quotient_relations : (∀ p : Fin 64, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 128, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 128, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 64, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 64)) := [[0,3,9],[1,2,8],[4,5,14],[6,7,15],[10,11,23],[12,13,26],[16,17,29],[18],[19,20,35],[21,22,36],[24,25,39],[27,28,44],[30,31,45],[32,33,34],[37,38,55],[40,41,48],[42,43,54],[46,47,60],[49,50,53],[51,52,61],[56,57,63],[58,59,62]]
noncomputable def verticesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (12)) (.leaf (13)))) (.branch 14 (.branch 13 (.leaf (15)) (.leaf (16))) (.branch 15 (.leaf (8)) (.leaf (11)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (18)) (.leaf (19))) (.branch 19 (.leaf (21)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (23)) (.leaf (25))) (.branch 23 (.leaf (26)) (.leaf (14))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (28)) (.leaf (29))) (.branch 27 (.leaf (17)) (.leaf (31)))) (.branch 30 (.branch 29 (.leaf (32)) (.leaf (20))) (.branch 31 (.leaf (34)) (.leaf (35))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (37)) (.leaf (38))) (.branch 35 (.leaf (39)) (.leaf (24)))) (.branch 38 (.branch 37 (.leaf (27)) (.leaf (40))) (.branch 39 (.leaf (41)) (.leaf (30))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (43)) (.leaf (44))) (.branch 43 (.leaf (46)) (.leaf (47)))) (.branch 46 (.branch 45 (.leaf (33)) (.leaf (36))) (.branch 47 (.leaf (49)) (.leaf (50)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (45)) (.leaf (52))) (.branch 51 (.leaf (53)) (.leaf (55)))) (.branch 54 (.branch 53 (.leaf (56)) (.leaf (54))) (.branch 55 (.leaf (48)) (.leaf (42))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (58)) (.leaf (59))) (.branch 59 (.leaf (61)) (.leaf (62)))) (.branch 62 (.branch 61 (.leaf (51)) (.leaf (57))) (.branch 63 (.leaf (63)) (.leaf (60))))))))
noncomputable def verticesIndex (p : Fin 64) : Fin 64 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (9)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (15)))) (.branch 14 (.branch 13 (.leaf (10)) (.leaf (11))) (.branch 15 (.leaf (23)) (.leaf (12)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (13)) (.leaf (26))) (.branch 19 (.leaf (16)) (.leaf (17)))) (.branch 22 (.branch 21 (.leaf (29)) (.leaf (18))) (.branch 23 (.leaf (19)) (.leaf (20))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (35)) (.leaf (21))) (.branch 27 (.leaf (22)) (.leaf (36)))) (.branch 30 (.branch 29 (.leaf (24)) (.leaf (25))) (.branch 31 (.leaf (39)) (.leaf (27))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (28)) (.leaf (44))) (.branch 35 (.leaf (30)) (.leaf (31)))) (.branch 38 (.branch 37 (.leaf (45)) (.leaf (32))) (.branch 39 (.leaf (33)) (.leaf (34))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (38))) (.branch 43 (.leaf (55)) (.leaf (40)))) (.branch 46 (.branch 45 (.leaf (41)) (.leaf (48))) (.branch 47 (.leaf (42)) (.leaf (43)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (54)) (.leaf (46))) (.branch 51 (.leaf (47)) (.leaf (60)))) (.branch 54 (.branch 53 (.leaf (49)) (.leaf (50))) (.branch 55 (.leaf (53)) (.leaf (51))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (52)) (.leaf (61))) (.branch 59 (.leaf (56)) (.leaf (57)))) (.branch 62 (.branch 61 (.leaf (63)) (.leaf (58))) (.branch 63 (.leaf (59)) (.leaf (62))))))))
noncomputable def verticesBack (p : Fin 64) : Fin 64 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 64, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 64 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 64, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 64)) := [[0,1],[2,4],[3,6],[5,9],[7,10],[8,12],[11,16],[13,18],[14,19],[15,21],[17,24],[20,27],[22,29],[23,30],[25,32],[26,33],[28,36],[31,37],[34,40],[35,42],[38,46],[39,48],[41,49],[43,51],[44,53],[45,54],[47,56],[50,55],[52,58],[57,61],[59,60],[62,63]]
noncomputable def edgesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (8))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (7))) (.branch 11 (.leaf (9)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (14))) (.branch 15 (.leaf (16)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (13)) (.leaf (20))) (.branch 19 (.leaf (15)) (.leaf (17)))) (.branch 22 (.branch 21 (.leaf (22)) (.leaf (19))) (.branch 23 (.leaf (24)) (.leaf (26))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (28))) (.branch 27 (.leaf (30)) (.leaf (23)))) (.branch 30 (.branch 29 (.leaf (32)) (.leaf (25))) (.branch 31 (.leaf (27)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (29)) (.leaf (31))) (.branch 35 (.leaf (36)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (35))) (.branch 39 (.leaf (40)) (.leaf (42))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (44))) (.branch 43 (.leaf (39)) (.leaf (46)))) (.branch 46 (.branch 45 (.leaf (48)) (.leaf (50))) (.branch 47 (.leaf (41)) (.leaf (52)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (43)) (.leaf (45))) (.branch 51 (.leaf (54)) (.leaf (47)))) (.branch 54 (.branch 53 (.leaf (56)) (.leaf (49))) (.branch 55 (.leaf (51)) (.leaf (55))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (53)) (.leaf (58))) (.branch 59 (.leaf (57)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (61)) (.leaf (59))) (.branch 63 (.leaf (62)) (.leaf (63))))))))
noncomputable def edgesIndex (p : Fin 64) : Fin 64 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (9))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (10))) (.branch 11 (.leaf (8)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (16))) (.branch 15 (.leaf (13)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (19))) (.branch 19 (.leaf (15)) (.leaf (21)))) (.branch 22 (.branch 21 (.leaf (17)) (.leaf (24))) (.branch 23 (.leaf (20)) (.leaf (27))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (22)) (.leaf (29))) (.branch 27 (.leaf (23)) (.leaf (30)))) (.branch 30 (.branch 29 (.leaf (25)) (.leaf (32))) (.branch 31 (.leaf (26)) (.leaf (33))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (28)) (.leaf (36))) (.branch 35 (.leaf (31)) (.leaf (37)))) (.branch 38 (.branch 37 (.leaf (34)) (.leaf (40))) (.branch 39 (.leaf (35)) (.leaf (42))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (38)) (.leaf (46))) (.branch 43 (.leaf (39)) (.leaf (48)))) (.branch 46 (.branch 45 (.leaf (41)) (.leaf (49))) (.branch 47 (.leaf (43)) (.leaf (51)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (44)) (.leaf (53))) (.branch 51 (.leaf (45)) (.leaf (54)))) (.branch 54 (.branch 53 (.leaf (47)) (.leaf (56))) (.branch 55 (.leaf (50)) (.leaf (55))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (52)) (.leaf (58))) (.branch 59 (.leaf (57)) (.leaf (61)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (60))) (.branch 63 (.leaf (62)) (.leaf (63))))))))
noncomputable def edgesBack (p : Fin 64) : Fin 64 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 64, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 64 := by decide +kernel
theorem edges_partition : ∀ p : Fin 64, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 64)) := [[0,2,5],[1,3,7,11,17,25,33,12],[4,8,13,18,26,34,41,50,37,45,42,19],[6,9,14,20,28,21],[10,15,22,16,23,31,38,47,57,51,54,30],[24,29,36,44,49,48],[27,35,43,52,59,46,55,53],[32,39,40],[56,60,62],[58,61,63]]
noncomputable def facesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (11)) (.leaf (2))) (.branch 7 (.leaf (23)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (24))) (.branch 11 (.leaf (29)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (10)) (.leaf (13))) (.branch 15 (.leaf (25)) (.leaf (30)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (32)) (.leaf (7))) (.branch 19 (.leaf (14)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (26)) (.leaf (28))) (.branch 23 (.leaf (31)) (.leaf (33))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (41)) (.leaf (8))) (.branch 27 (.leaf (15)) (.leaf (47)))) (.branch 30 (.branch 29 (.leaf (27)) (.leaf (42))) (.branch 31 (.leaf (40)) (.leaf (34))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (55)) (.leaf (9))) (.branch 35 (.leaf (16)) (.leaf (48)))) (.branch 38 (.branch 37 (.leaf (43)) (.leaf (19))) (.branch 39 (.leaf (35)) (.leaf (56))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (57)) (.leaf (17))) (.branch 43 (.leaf (21)) (.leaf (49)))) (.branch 46 (.branch 45 (.leaf (44)) (.leaf (20))) (.branch 47 (.leaf (52)) (.leaf (36)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (46)) (.leaf (45))) (.branch 51 (.leaf (18)) (.leaf (38)))) (.branch 54 (.branch 53 (.leaf (50)) (.leaf (54))) (.branch 55 (.leaf (39)) (.leaf (53))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (58)) (.leaf (37))) (.branch 59 (.leaf (61)) (.leaf (51)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (62))) (.branch 63 (.leaf (60)) (.leaf (63))))))))
noncomputable def facesIndex (p : Fin 64) : Fin 64 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (7))) (.branch 7 (.leaf (11)) (.leaf (17))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (25)) (.leaf (33))) (.branch 11 (.leaf (12)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (13))) (.branch 15 (.leaf (18)) (.leaf (26)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (34)) (.leaf (41))) (.branch 19 (.leaf (50)) (.leaf (37)))) (.branch 22 (.branch 21 (.leaf (45)) (.leaf (42))) (.branch 23 (.leaf (19)) (.leaf (6))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (9)) (.leaf (14))) (.branch 27 (.leaf (20)) (.leaf (28)))) (.branch 30 (.branch 29 (.leaf (21)) (.leaf (10))) (.branch 31 (.leaf (15)) (.leaf (22))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (16)) (.leaf (23))) (.branch 35 (.leaf (31)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (47)) (.leaf (57))) (.branch 39 (.leaf (51)) (.leaf (54))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (30)) (.leaf (24))) (.branch 43 (.leaf (29)) (.leaf (36)))) (.branch 46 (.branch 45 (.leaf (44)) (.leaf (49))) (.branch 47 (.leaf (48)) (.leaf (27)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (35)) (.leaf (43))) (.branch 51 (.leaf (52)) (.leaf (59)))) (.branch 54 (.branch 53 (.leaf (46)) (.leaf (55))) (.branch 55 (.leaf (53)) (.leaf (32))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (39)) (.leaf (40))) (.branch 59 (.leaf (56)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (62)) (.leaf (58))) (.branch 63 (.leaf (61)) (.leaf (63))))))))
noncomputable def facesBack (p : Fin 64) : Fin 64 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 64, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 64 := by decide +kernel
theorem faces_partition : ∀ p : Fin 64, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [3,8,12,6,12,6,8,3,3,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 1 : Int) = 22 - 32 + 10 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 1 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.leaf (⟨0,1,-1,-2⟩))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 11 (.leaf (⟨1,0,-2,1⟩)) (.leaf (⟨0,-1,1,3⟩)))) (.branch 14 (.branch 13 (.leaf (⟨0,1,-1,1⟩)) (.leaf (⟨1,1,1,2⟩))) (.branch 15 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨1,1,-2,-1⟩)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (⟨-1,0,3,-1⟩)) (.leaf (⟨0,1,-1,-4⟩))) (.branch 19 (.leaf (⟨1,-1,2,-1⟩)) (.leaf (⟨1,-2,1,-1⟩)))) (.branch 22 (.branch 21 (.leaf (⟨-2,-3,-1,-2⟩)) (.leaf (⟨1,-1,-1,2⟩))) (.branch 23 (.leaf (⟨-1,-2,2,3⟩)) (.leaf (⟨-1,-1,3,2⟩))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (⟨1,0,4,1⟩)) (.leaf (⟨0,1,-1,3⟩))) (.branch 27 (.leaf (⟨1,0,2,1⟩)) (.leaf (⟨-3,2,-2,1⟩)))) (.branch 30 (.branch 29 (.leaf (⟨2,5,1,3⟩)) (.leaf (⟨1,1,-4,-3⟩))) (.branch 31 (.leaf (⟨-1,1,2,-3⟩)) (.leaf (⟨1,2,-3,-5⟩))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (⟨-1,0,-3,-1⟩)) (.leaf (⟨0,-1,1,-2⟩))) (.branch 35 (.leaf (⟨-1,-1,-2,-3⟩)) (.leaf (⟨-3,-1,-2,-1⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-2,-1,3,1⟩)) (.leaf (⟨2,-1,-5,3⟩))) (.branch 39 (.leaf (⟨-1,-3,3,8⟩)) (.leaf (⟨1,1,3,4⟩))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (⟨-1,1,-3,2⟩)) (.leaf (⟨1,2,2,5⟩))) (.branch 43 (.leaf (⟨-1,3,-1,2⟩)) (.leaf (⟨3,4,2,3⟩)))) (.branch 46 (.branch 45 (.leaf (⟨5,3,3,2⟩)) (.leaf (⟨2,1,-5,-2⟩))) (.branch 47 (.leaf (⟨-3,1,8,-3⟩)) (.leaf (⟨1,4,-3,-11⟩)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (⟨2,1,5,3⟩)) (.leaf (⟨-5,-8,-3,-5⟩))) (.branch 51 (.leaf (⟨-8,-3,-5,-2⟩)) (.leaf (⟨4,-3,3,-2⟩)))) (.branch 54 (.branch 53 (.leaf (⟨-3,-7,-2,-5⟩)) (.leaf (⟨3,-5,2,-3⟩))) (.branch 55 (.leaf (⟨4,1,3,1⟩)) (.leaf (⟨-3,-2,8,5⟩))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (⟨11,4,8,3⟩)) (.leaf (⟨-4,7,-3,5⟩))) (.branch 59 (.leaf (⟨-7,3,-5,2⟩)) (.leaf (⟨3,10,2,7⟩)))) (.branch 62 (.branch 61 (.leaf (⟨4,3,-11,-8⟩)) (.leaf (⟨-7,-4,-5,-3⟩))) (.branch 63 (.leaf (⟨10,7,7,5⟩)) (.leaf (⟨7,11,5,8⟩))))))))
noncomputable def liftMatrix (p : Fin 64) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 64) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],10⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],11⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],12⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],13⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],14⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],15⟩,⟨⟨-1,0,3,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],16⟩,⟨⟨0,1,-1,-4⟩,[.t (0),.s,.t (4)],17⟩,⟨⟨1,-1,2,-1⟩,[.t (0),.s,.t (-2),.s,.t (-1)],18⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],19⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],20⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],21⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],22⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],23⟩,⟨⟨1,0,4,1⟩,[.t (0),.s,.t (-4),.s,.t (0)],24⟩,⟨⟨0,1,-1,3⟩,[.t (0),.s,.t (-3)],25⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],26⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],27⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],28⟩,⟨⟨1,1,-4,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],29⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],30⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],31⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],32⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],33⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],34⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],35⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],36⟩,⟨⟨2,-1,-5,3⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-1)],37⟩,⟨⟨-1,-3,3,8⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (2)],38⟩,⟨⟨1,1,3,4⟩,[.t (0),.s,.t (-3),.s,.t (1)],39⟩,⟨⟨-1,1,-3,2⟩,[.t (0),.s,.t (-3),.s,.t (-1)],40⟩,⟨⟨1,2,2,5⟩,[.t (0),.s,.t (-2),.s,.t (2)],41⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],42⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],43⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],44⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],45⟩,⟨⟨-3,1,8,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],46⟩,⟨⟨1,4,-3,-11⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (3)],47⟩,⟨⟨2,1,5,3⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (0)],48⟩,⟨⟨-5,-8,-3,-5⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (1)],49⟩,⟨⟨-8,-3,-5,-2⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (0)],50⟩,⟨⟨4,-3,3,-2⟩,[.t (1),.s,.t (-3),.s,.t (-1)],51⟩,⟨⟨-3,-7,-2,-5⟩,[.t (1),.s,.t (-2),.s,.t (2)],52⟩,⟨⟨3,-5,2,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2)],53⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],54⟩,⟨⟨-3,-2,8,5⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],55⟩,⟨⟨11,4,8,3⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (0)],56⟩,⟨⟨-4,7,-3,5⟩,[.t (1),.s,.t (-3),.s,.t (-2)],57⟩,⟨⟨-7,3,-5,2⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-1)],58⟩,⟨⟨3,10,2,7⟩,[.t (1),.s,.t (-2),.s,.t (3)],59⟩,⟨⟨4,3,-11,-8⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],60⟩,⟨⟨-7,-4,-5,-3⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (0)],61⟩,⟨⟨10,7,7,5⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],62⟩,⟨⟨7,11,5,8⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (1)],63⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 64 ∧ ((List.finRange 64).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 64) := [⟨9,1,⟨⟨-1,-3,0,-1⟩,[.t (3)],0⟩⟩,⟨36,4,⟨⟨-11,-9,-6,-5⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨22,3,⟨⟨5,3,-17,-10⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨45,7,⟨⟨-22,-9,-17,-7⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨55,9,⟨⟨79,30,50,19⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨60,10,⟨⟨113,42,78,29⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨47,8,⟨⟨-77,-27,-57,-20⟩,[.t (1),.s,.t (-3),.s,.t (-7),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨29,3,⟨⟨-10,-3,17,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨17,2,⟨⟨-1,0,-8,-1⟩,[.t (0),.s,.t (-8),.s,.t (0)],0⟩⟩,⟨24,2,⟨⟨-1,0,8,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨39,5,⟨⟨10,-3,27,-8⟩,[.t (0),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨48,5,⟨⟨-8,3,-27,10⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨41,6,⟨⟨-50,21,-31,13⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨18,-3,⟨⟨5,-3,7,-4⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨54,7,⟨⟨-7,9,17,-22⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨56,8,⟨⟨-20,27,57,-77⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨63,11,⟨⟨-106,147,-75,104⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨62,11,⟨⟨104,-147,75,-106⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨59,10,⟨⟨29,-42,-78,113⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨50,9,⟨⟨19,-30,-50,79⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨49,6,⟨⟨13,-21,31,-50⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨28,4,⟨⟨-5,9,6,-11⟩,[.t (-1),.s,.t (-6),.s,.t (-2)],0⟩⟩,⟨5,1,⟨⟨-1,3,0,-1⟩,[.t (-3)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-2,3),(-1,2),(-2,5),(-3,8),(-4,11),(-1,3),(-1,4),(0,1),(1,4),(1,3),(2,5),(1,2),(1,1),(4,3),(11,8),(7,5),(10,7),(3,2),(8,5),(5,3),(2,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G192_4_c2

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
