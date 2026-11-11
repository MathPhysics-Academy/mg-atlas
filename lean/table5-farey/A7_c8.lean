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
namespace A7_c8
noncomputable def originalSData : LookupTree (Fin 120) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (9))) (.branch 6 (.leaf (8)) (.leaf (12))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (0)) (.leaf (14))) (.branch 10 (.leaf (13)) (.leaf (16)))) (.branch 13 (.branch 12 (.leaf (17)) (.leaf (15))) (.branch 14 (.leaf (20)) (.leaf (2)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (23)) (.branch 17 (.leaf (21)) (.leaf (22)))) (.branch 20 (.branch 19 (.leaf (25)) (.leaf (27))) (.branch 21 (.leaf (4)) (.leaf (29))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (30)) (.leaf (6))) (.branch 25 (.leaf (33)) (.leaf (31)))) (.branch 28 (.branch 27 (.leaf (35)) (.leaf (32))) (.branch 29 (.leaf (37)) (.leaf (10))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (11)) (.branch 32 (.leaf (40)) (.leaf (42)))) (.branch 35 (.branch 34 (.leaf (39)) (.leaf (44))) (.branch 36 (.leaf (41)) (.leaf (45))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (43)) (.leaf (48))) (.branch 40 (.leaf (50)) (.leaf (18)))) (.branch 43 (.branch 42 (.leaf (52)) (.leaf (19))) (.branch 44 (.leaf (54)) (.leaf (51)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (53)) (.branch 47 (.leaf (58)) (.leaf (46)))) (.branch 50 (.branch 49 (.leaf (55)) (.leaf (61))) (.branch 51 (.leaf (24)) (.leaf (62))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (26)) (.leaf (63))) (.branch 55 (.leaf (28)) (.leaf (65)))) (.branch 58 (.branch 57 (.leaf (49)) (.leaf (68))) (.branch 59 (.leaf (64)) (.leaf (71)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (73)) (.branch 62 (.leaf (66)) (.leaf (34)))) (.branch 65 (.branch 64 (.leaf (36)) (.leaf (47))) (.branch 66 (.leaf (38)) (.leaf (56))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (78)) (.leaf (76))) (.branch 70 (.leaf (80)) (.leaf (81)))) (.branch 73 (.branch 72 (.leaf (70)) (.leaf (83))) (.branch 74 (.leaf (77)) (.leaf (85)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (86)) (.branch 77 (.leaf (88)) (.leaf (90)))) (.branch 80 (.branch 79 (.leaf (75)) (.leaf (92))) (.branch 81 (.leaf (89)) (.leaf (59))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (95)) (.leaf (82))) (.branch 85 (.leaf (97)) (.leaf (91)))) (.branch 88 (.branch 87 (.leaf (67)) (.leaf (100))) (.branch 89 (.leaf (57)) (.leaf (102))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (60)) (.branch 92 (.leaf (103)) (.leaf (87)))) (.branch 95 (.branch 94 (.leaf (104)) (.leaf (93))) (.branch 96 (.leaf (72)) (.leaf (106))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (96)) (.leaf (109))) (.branch 100 (.leaf (98)) (.leaf (79)))) (.branch 103 (.branch 102 (.leaf (94)) (.leaf (69))) (.branch 104 (.leaf (74)) (.leaf (101)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (112)) (.branch 107 (.leaf (84)) (.leaf (99)))) (.branch 110 (.branch 109 (.leaf (113)) (.leaf (107))) (.branch 111 (.leaf (117)) (.leaf (118))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (111)) (.leaf (114))) (.branch 115 (.leaf (119)) (.leaf (110)))) (.branch 118 (.branch 117 (.leaf (115)) (.leaf (116))) (.branch 119 (.leaf (105)) (.leaf (108)))))))))
noncomputable def originalS (p : Fin 120) : Fin 120 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 120) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 5 (.branch 4 (.leaf (8)) (.leaf (10))) (.branch 6 (.leaf (11)) (.leaf (0))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (13)) (.leaf (15))) (.branch 10 (.leaf (12)) (.leaf (17)))) (.branch 13 (.branch 12 (.leaf (18)) (.leaf (19))) (.branch 14 (.leaf (21)) (.leaf (22)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (3)) (.branch 17 (.leaf (24)) (.leaf (1)))) (.branch 20 (.branch 19 (.leaf (26)) (.leaf (28))) (.branch 21 (.leaf (23)) (.leaf (30))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (31)) (.leaf (32))) (.branch 25 (.leaf (34)) (.leaf (29)))) (.branch 28 (.branch 27 (.leaf (36)) (.leaf (5))) (.branch 29 (.leaf (38)) (.leaf (39))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (7)) (.branch 32 (.leaf (41)) (.leaf (43)))) (.branch 35 (.branch 34 (.leaf (9)) (.leaf (40))) (.branch 36 (.leaf (44)) (.leaf (46))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (47)) (.leaf (49))) (.branch 40 (.leaf (51)) (.leaf (16)))) (.branch 43 (.branch 42 (.leaf (53)) (.leaf (14))) (.branch 44 (.leaf (55)) (.leaf (56)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (57)) (.branch 47 (.leaf (27)) (.leaf (59)))) (.branch 50 (.branch 49 (.leaf (60)) (.leaf (33))) (.branch 51 (.leaf (20)) (.leaf (25))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (62)) (.leaf (64))) (.branch 55 (.leaf (58)) (.leaf (66)))) (.branch 58 (.branch 57 (.leaf (67)) (.leaf (69))) (.branch 59 (.leaf (70)) (.leaf (72)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (74)) (.branch 62 (.leaf (75)) (.leaf (61)))) (.branch 65 (.branch 64 (.leaf (76)) (.leaf (42))) (.branch 66 (.leaf (77)) (.leaf (50))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (79)) (.leaf (35))) (.branch 70 (.leaf (81)) (.leaf (82)))) (.branch 73 (.branch 72 (.leaf (63)) (.leaf (84))) (.branch 74 (.leaf (37)) (.leaf (86)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (87)) (.branch 77 (.leaf (89)) (.leaf (91)))) (.branch 80 (.branch 79 (.leaf (65)) (.leaf (93))) (.branch 81 (.leaf (94)) (.leaf (45))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (96)) (.leaf (80))) (.branch 85 (.leaf (98)) (.leaf (99)))) (.branch 88 (.branch 87 (.leaf (48)) (.leaf (101))) (.branch 89 (.leaf (52)) (.leaf (71))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (54)) (.branch 92 (.leaf (78)) (.leaf (85)))) (.branch 95 (.branch 94 (.leaf (68)) (.leaf (105))) (.branch 96 (.leaf (102)) (.leaf (107))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (108)) (.leaf (73))) (.branch 100 (.leaf (110)) (.leaf (103)))) (.branch 103 (.branch 102 (.leaf (88)) (.leaf (104))) (.branch 104 (.leaf (109)) (.leaf (111)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (113)) (.branch 107 (.leaf (114)) (.leaf (90)))) (.branch 110 (.branch 109 (.leaf (115)) (.leaf (116))) (.branch 111 (.leaf (118)) (.leaf (119))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (100)) (.leaf (83))) (.branch 115 (.leaf (117)) (.leaf (97)))) (.branch 118 (.branch 117 (.leaf (112)) (.leaf (106))) (.branch 119 (.leaf (92)) (.leaf (95)))))))))
noncomputable def originalT (p : Fin 120) : Fin 120 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 60) :=
  (.branch 60 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (0)) (.leaf (3))) (.branch 6 (.leaf (4)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (1)) (.leaf (2))) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (9))) (.branch 14 (.leaf (3)) (.leaf (4)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 21 (.leaf (6)) (.leaf (7))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (8)) (.leaf (9))) (.branch 25 (.leaf (14)) (.leaf (15)))) (.branch 28 (.branch 27 (.leaf (16)) (.leaf (17))) (.branch 29 (.leaf (18)) (.leaf (10))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (11)) (.branch 32 (.leaf (12)) (.leaf (13)))) (.branch 35 (.branch 34 (.leaf (19)) (.leaf (20))) (.branch 36 (.leaf (21)) (.leaf (22))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (23)) (.leaf (24))) (.branch 40 (.leaf (14)) (.leaf (15)))) (.branch 43 (.branch 42 (.leaf (16)) (.leaf (17))) (.branch 44 (.leaf (18)) (.leaf (25)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (26)) (.branch 47 (.leaf (27)) (.leaf (28)))) (.branch 50 (.branch 49 (.leaf (29)) (.leaf (30))) (.branch 51 (.leaf (19)) (.leaf (20))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (21)) (.leaf (22))) (.branch 55 (.leaf (23)) (.leaf (24)))) (.branch 58 (.branch 57 (.leaf (31)) (.leaf (32))) (.branch 59 (.leaf (28)) (.leaf (33)))))))) (.branch 90 (.branch 75 (.branch 67 (.branch 63 (.branch 61 (.leaf (34)) (.branch 62 (.leaf (31)) (.leaf (25)))) (.branch 65 (.branch 64 (.leaf (26)) (.leaf (27))) (.branch 66 (.leaf (29)) (.leaf (30))))) (.branch 71 (.branch 69 (.branch 68 (.leaf (35)) (.leaf (36))) (.branch 70 (.leaf (37)) (.leaf (33)))) (.branch 73 (.branch 72 (.leaf (38)) (.leaf (39))) (.branch 74 (.leaf (40)) (.leaf (41)))))) (.branch 82 (.branch 78 (.branch 76 (.leaf (35)) (.branch 77 (.leaf (32)) (.leaf (34)))) (.branch 80 (.branch 79 (.leaf (42)) (.leaf (43))) (.branch 81 (.leaf (44)) (.leaf (38))))) (.branch 86 (.branch 84 (.branch 83 (.leaf (39)) (.leaf (45))) (.branch 85 (.leaf (46)) (.leaf (47)))) (.branch 88 (.branch 87 (.leaf (42)) (.leaf (43))) (.branch 89 (.leaf (36)) (.leaf (37))))))) (.branch 105 (.branch 97 (.branch 93 (.branch 91 (.leaf (40)) (.branch 92 (.leaf (41)) (.leaf (48)))) (.branch 95 (.branch 94 (.leaf (49)) (.leaf (50))) (.branch 96 (.leaf (45)) (.leaf (46))))) (.branch 101 (.branch 99 (.branch 98 (.leaf (51)) (.leaf (52))) (.branch 100 (.leaf (53)) (.leaf (48)))) (.branch 103 (.branch 102 (.leaf (49)) (.leaf (44))) (.branch 104 (.leaf (47)) (.leaf (50)))))) (.branch 112 (.branch 108 (.branch 106 (.leaf (54)) (.branch 107 (.leaf (51)) (.leaf (52)))) (.branch 110 (.branch 109 (.leaf (55)) (.leaf (53))) (.branch 111 (.leaf (56)) (.leaf (54))))) (.branch 116 (.branch 114 (.branch 113 (.leaf (57)) (.leaf (58))) (.branch 115 (.leaf (55)) (.leaf (59)))) (.branch 118 (.branch 117 (.leaf (56)) (.leaf (59))) (.branch 119 (.leaf (57)) (.leaf (58)))))))))
noncomputable def projection (p : Fin 120) : Fin 60 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 120) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (5))) (.branch 6 (.leaf (6)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (10)) (.leaf (11))) (.branch 10 (.leaf (12)) (.leaf (16)))) (.branch 13 (.branch 12 (.leaf (17)) (.leaf (18))) (.branch 14 (.leaf (19)) (.leaf (24)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (25)) (.branch 17 (.leaf (26)) (.leaf (27)))) (.branch 20 (.branch 19 (.leaf (28)) (.leaf (33))) (.branch 21 (.leaf (34)) (.leaf (35))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (36)) (.leaf (37))) (.branch 25 (.leaf (38)) (.leaf (44)))) (.branch 28 (.branch 27 (.leaf (45)) (.leaf (46))) (.branch 29 (.leaf (47)) (.leaf (48))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (49)) (.branch 32 (.leaf (56)) (.leaf (57)))) (.branch 35 (.branch 34 (.leaf (59)) (.leaf (60))) (.branch 36 (.leaf (67)) (.leaf (68))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (69)) (.leaf (71))) (.branch 40 (.leaf (72)) (.leaf (73)))) (.branch 43 (.branch 42 (.leaf (74)) (.leaf (78))) (.branch 44 (.leaf (79)) (.leaf (80)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (83)) (.branch 47 (.leaf (84)) (.leaf (85)))) (.branch 50 (.branch 49 (.leaf (92)) (.leaf (93))) (.branch 51 (.leaf (94)) (.leaf (97))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (98)) (.leaf (99))) (.branch 55 (.leaf (105)) (.leaf (108)))) (.branch 58 (.branch 57 (.leaf (110)) (.leaf (112))) (.branch 59 (.leaf (113)) (.leaf (115))))))))
noncomputable def representative (p : Fin 60) : Fin 120 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (2))) (.branch 6 (.leaf (9)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (10)) (.leaf (11))) (.branch 10 (.leaf (5)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (15))) (.branch 14 (.leaf (17)) (.leaf (19)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (12)) (.branch 17 (.leaf (21)) (.leaf (13)))) (.branch 20 (.branch 19 (.leaf (23)) (.leaf (14))) (.branch 21 (.leaf (25)) (.leaf (16))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (26)) (.leaf (18))) (.branch 25 (.leaf (29)) (.leaf (20)))) (.branch 28 (.branch 27 (.leaf (22)) (.leaf (28))) (.branch 29 (.leaf (27)) (.leaf (24))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (31)) (.branch 32 (.leaf (30)) (.leaf (36)))) (.branch 35 (.branch 34 (.leaf (38)) (.leaf (40))) (.branch 36 (.leaf (42)) (.leaf (32))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (44)) (.leaf (33))) (.branch 40 (.leaf (45)) (.leaf (34)))) (.branch 43 (.branch 42 (.leaf (47)) (.leaf (35))) (.branch 44 (.leaf (48)) (.leaf (37)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (39)) (.branch 47 (.leaf (51)) (.leaf (41)))) (.branch 50 (.branch 49 (.leaf (43)) (.leaf (50))) (.branch 51 (.leaf (49)) (.leaf (46))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (53)) (.leaf (52))) (.branch 55 (.leaf (57)) (.leaf (58)))) (.branch 58 (.branch 57 (.leaf (59)) (.leaf (54))) (.branch 59 (.leaf (55)) (.leaf (56))))))))
noncomputable def S (p : Fin 60) : Fin 60 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (8))) (.branch 6 (.leaf (0)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (11)) (.leaf (12))) (.branch 10 (.leaf (13)) (.leaf (14)))) (.branch 13 (.branch 12 (.leaf (1)) (.leaf (16))) (.branch 14 (.leaf (18)) (.leaf (20)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (10)) (.branch 17 (.leaf (22)) (.leaf (4)))) (.branch 20 (.branch 19 (.leaf (24)) (.leaf (6))) (.branch 21 (.leaf (15)) (.leaf (25))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (27)) (.leaf (28))) (.branch 25 (.leaf (30)) (.leaf (31)))) (.branch 28 (.branch 27 (.leaf (32)) (.leaf (17))) (.branch 29 (.leaf (33)) (.leaf (34))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (19)) (.branch 32 (.leaf (35)) (.leaf (37)))) (.branch 35 (.branch 34 (.leaf (39)) (.leaf (41))) (.branch 36 (.leaf (43)) (.leaf (21))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (38)) (.leaf (26))) (.branch 40 (.leaf (46)) (.leaf (23)))) (.branch 43 (.branch 42 (.leaf (42)) (.leaf (29))) (.branch 44 (.leaf (49)) (.leaf (50)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (44)) (.branch 47 (.leaf (52)) (.leaf (53)))) (.branch 50 (.branch 49 (.leaf (47)) (.leaf (36))) (.branch 51 (.leaf (54)) (.leaf (55))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (40)) (.leaf (56))) (.branch 55 (.leaf (58)) (.leaf (59)))) (.branch 58 (.branch 57 (.leaf (57)) (.leaf (48))) (.branch 59 (.leaf (45)) (.leaf (51))))))))
noncomputable def T (p : Fin 60) : Fin 60 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (5)) (.branch 2 (.leaf (11)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (17))) (.branch 6 (.leaf (2)) (.leaf (19))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (6)) (.leaf (15)))) (.branch 13 (.branch 12 (.leaf (7)) (.leaf (8))) (.branch 14 (.leaf (9)) (.leaf (10)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (20)) (.branch 17 (.leaf (12)) (.leaf (27)))) (.branch 20 (.branch 19 (.leaf (13)) (.leaf (30))) (.branch 21 (.leaf (14)) (.leaf (36))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (16)) (.leaf (40))) (.branch 25 (.leaf (18)) (.leaf (21)))) (.branch 28 (.branch 27 (.leaf (38)) (.leaf (22))) (.branch 29 (.leaf (23)) (.leaf (42))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (24)) (.branch 32 (.leaf (25)) (.leaf (26)))) (.branch 35 (.branch 34 (.leaf (28)) (.leaf (29))) (.branch 36 (.leaf (31)) (.leaf (49))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (32)) (.leaf (37))) (.branch 40 (.leaf (33)) (.leaf (52)))) (.branch 43 (.branch 42 (.leaf (34)) (.leaf (41))) (.branch 44 (.leaf (35)) (.leaf (45)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (58)) (.branch 47 (.leaf (39)) (.leaf (48)))) (.branch 50 (.branch 49 (.leaf (57)) (.leaf (43))) (.branch 51 (.leaf (44)) (.leaf (59))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (46)) (.leaf (47))) (.branch 55 (.leaf (50)) (.leaf (51)))) (.branch 58 (.branch 57 (.leaf (53)) (.leaf (56))) (.branch 59 (.leaf (54)) (.leaf (55))))))))
noncomputable def Ti (p : Fin 60) : Fin 60 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 60) : Fin 60 := T (S p)
theorem quotient_relations : (∀ p : Fin 60, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 120, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 120, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 60, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 60)) := [[0,3,9],[1,2,8],[4,5,13],[6,7,14],[10,11,12],[15,16,25],[17,18,28],[19,20,31],[21,22,32],[23,24,34],[26,27,33],[29,30,35],[36,37,50],[38,39,44],[40,41,53],[42,43,47],[45,46,55],[48,49,54],[51,52,56],[57,58,59]]
noncomputable def verticesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (7)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (10)) (.leaf (5))) (.branch 10 (.leaf (2)) (.leaf (12)))) (.branch 13 (.branch 12 (.leaf (13)) (.leaf (14))) (.branch 14 (.leaf (8)) (.leaf (11)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (18)))) (.branch 20 (.branch 19 (.leaf (19)) (.leaf (21))) (.branch 21 (.leaf (22)) (.leaf (24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (25)) (.leaf (27))) (.branch 25 (.leaf (28)) (.leaf (17)))) (.branch 28 (.branch 27 (.leaf (30)) (.leaf (31))) (.branch 29 (.leaf (20)) (.leaf (33))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (34)) (.branch 32 (.leaf (23)) (.leaf (26)))) (.branch 35 (.branch 34 (.leaf (32)) (.leaf (29))) (.branch 36 (.leaf (35)) (.leaf (36))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (37)) (.leaf (39))) (.branch 40 (.leaf (40)) (.leaf (42)))) (.branch 43 (.branch 42 (.leaf (43)) (.leaf (45))) (.branch 44 (.leaf (46)) (.leaf (41)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (48)) (.branch 47 (.leaf (49)) (.leaf (47)))) (.branch 50 (.branch 49 (.leaf (51)) (.leaf (52))) (.branch 51 (.leaf (38)) (.leaf (54))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (55)) (.leaf (44))) (.branch 55 (.leaf (53)) (.leaf (50)))) (.branch 58 (.branch 57 (.leaf (56)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (59))))))))
noncomputable def verticesIndex (p : Fin 60) : Fin 60 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (9)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (8)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (13))) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (14)) (.leaf (10))) (.branch 14 (.leaf (11)) (.leaf (12)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (25)))) (.branch 20 (.branch 19 (.leaf (17)) (.leaf (18))) (.branch 21 (.leaf (28)) (.leaf (19))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (20)) (.leaf (31))) (.branch 25 (.leaf (21)) (.leaf (22)))) (.branch 28 (.branch 27 (.leaf (32)) (.leaf (23))) (.branch 29 (.leaf (24)) (.leaf (34))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (26)) (.branch 32 (.leaf (27)) (.leaf (33)))) (.branch 35 (.branch 34 (.leaf (29)) (.leaf (30))) (.branch 36 (.leaf (35)) (.leaf (36))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (37)) (.leaf (50))) (.branch 40 (.leaf (38)) (.leaf (39)))) (.branch 43 (.branch 42 (.leaf (44)) (.leaf (40))) (.branch 44 (.leaf (41)) (.leaf (53)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (42)) (.branch 47 (.leaf (43)) (.leaf (47)))) (.branch 50 (.branch 49 (.leaf (45)) (.leaf (46))) (.branch 51 (.leaf (55)) (.leaf (48))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (49)) (.leaf (54))) (.branch 55 (.leaf (51)) (.leaf (52)))) (.branch 58 (.branch 57 (.leaf (56)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (59))))))))
noncomputable def verticesBack (p : Fin 60) : Fin 60 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 60, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 60 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 60, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 60)) := [[0,1],[2,4],[3,6],[5,9],[7,10],[8,11],[12,15],[13,17],[14,19],[16,21],[18,23],[20,25],[22,26],[24,29],[27,28],[30,31],[32,36],[33,38],[34,40],[35,42],[37,44],[39,45],[41,47],[43,48],[46,51],[49,50],[52,53],[54,57],[55,58],[56,59]]
noncomputable def edgesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (8)) (.leaf (10))) (.branch 10 (.leaf (7)) (.leaf (9)))) (.branch 13 (.branch 12 (.leaf (11)) (.leaf (12))) (.branch 14 (.leaf (14)) (.leaf (16)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (13)) (.branch 17 (.leaf (18)) (.leaf (15)))) (.branch 20 (.branch 19 (.leaf (20)) (.leaf (17))) (.branch 21 (.leaf (22)) (.leaf (19))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (24)) (.leaf (21))) (.branch 25 (.leaf (26)) (.leaf (23)))) (.branch 28 (.branch 27 (.leaf (25)) (.leaf (28))) (.branch 29 (.leaf (29)) (.leaf (27))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (30)) (.branch 32 (.leaf (31)) (.leaf (32)))) (.branch 35 (.branch 34 (.leaf (34)) (.leaf (36))) (.branch 36 (.leaf (38)) (.leaf (33))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (40)) (.leaf (35))) (.branch 40 (.leaf (42)) (.leaf (37)))) (.branch 43 (.branch 42 (.leaf (44)) (.leaf (39))) (.branch 44 (.leaf (46)) (.leaf (41)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (43)) (.branch 47 (.leaf (48)) (.leaf (45)))) (.branch 50 (.branch 49 (.leaf (47)) (.leaf (50))) (.branch 51 (.leaf (51)) (.leaf (49))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (52)) (.leaf (53))) (.branch 55 (.leaf (54)) (.leaf (56)))) (.branch 58 (.branch 57 (.leaf (58)) (.leaf (55))) (.branch 59 (.leaf (57)) (.leaf (59))))))))
noncomputable def edgesIndex (p : Fin 60) : Fin 60 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (9)) (.leaf (7))) (.branch 10 (.leaf (10)) (.leaf (8)))) (.branch 13 (.branch 12 (.leaf (11)) (.leaf (12))) (.branch 14 (.leaf (15)) (.leaf (13)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (17)) (.branch 17 (.leaf (14)) (.leaf (19)))) (.branch 20 (.branch 19 (.leaf (16)) (.leaf (21))) (.branch 21 (.leaf (18)) (.leaf (23))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (20)) (.leaf (25))) (.branch 25 (.leaf (22)) (.leaf (26)))) (.branch 28 (.branch 27 (.leaf (24)) (.leaf (29))) (.branch 29 (.leaf (27)) (.leaf (28))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (30)) (.branch 32 (.leaf (31)) (.leaf (32)))) (.branch 35 (.branch 34 (.leaf (36)) (.leaf (33))) (.branch 36 (.leaf (38)) (.leaf (34))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (40)) (.leaf (35))) (.branch 40 (.leaf (42)) (.leaf (37)))) (.branch 43 (.branch 42 (.leaf (44)) (.leaf (39))) (.branch 44 (.leaf (45)) (.leaf (41)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (47)) (.branch 47 (.leaf (43)) (.leaf (48)))) (.branch 50 (.branch 49 (.leaf (46)) (.leaf (51))) (.branch 51 (.leaf (49)) (.leaf (50))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (52)) (.leaf (53))) (.branch 55 (.leaf (54)) (.leaf (57)))) (.branch 58 (.branch 57 (.leaf (55)) (.leaf (58))) (.branch 59 (.leaf (56)) (.leaf (59))))))))
noncomputable def edgesBack (p : Fin 60) : Fin 60 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 60, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 60 := by decide +kernel
theorem edges_partition : ∀ p : Fin 60, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 60)) := [[0,2,5],[1,3,7,11],[4,8,12,16,22,27,17],[6,9,13,18,24,30,19],[10,14,20,15],[21,25,31,35,43,49,36],[23,28,33,39,46,52,40],[26,32,37,38],[29,34,41,42],[44,50,54,58,45],[47,53,56,57,48],[51,55,59]]
noncomputable def facesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (7))) (.branch 6 (.leaf (2)) (.leaf (14))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (8))) (.branch 10 (.leaf (15)) (.leaf (21)))) (.branch 13 (.branch 12 (.leaf (6)) (.leaf (9))) (.branch 14 (.leaf (16)) (.leaf (22)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (24)) (.branch 17 (.leaf (10)) (.leaf (13)))) (.branch 20 (.branch 19 (.leaf (17)) (.leaf (20))) (.branch 21 (.leaf (23)) (.leaf (25))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (11)) (.leaf (32))) (.branch 25 (.leaf (18)) (.leaf (26)))) (.branch 28 (.branch 27 (.leaf (39)) (.leaf (12))) (.branch 29 (.leaf (33)) (.leaf (43))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (19)) (.branch 32 (.leaf (27)) (.leaf (40)))) (.branch 35 (.branch 34 (.leaf (34)) (.leaf (44))) (.branch 36 (.leaf (28)) (.leaf (31))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (41)) (.leaf (42))) (.branch 40 (.leaf (35)) (.leaf (38)))) (.branch 43 (.branch 42 (.leaf (45)) (.leaf (46))) (.branch 44 (.leaf (29)) (.leaf (47)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (51)) (.branch 47 (.leaf (36)) (.leaf (52)))) (.branch 50 (.branch 49 (.leaf (56)) (.leaf (30))) (.branch 51 (.leaf (48)) (.leaf (57))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (37)) (.leaf (53))) (.branch 55 (.leaf (49)) (.leaf (58)))) (.branch 58 (.branch 57 (.leaf (54)) (.leaf (55))) (.branch 59 (.leaf (50)) (.leaf (59))))))))
noncomputable def facesIndex (p : Fin 60) : Fin 60 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (3))) (.branch 6 (.leaf (7)) (.leaf (11))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (4)) (.leaf (8))) (.branch 10 (.leaf (12)) (.leaf (16)))) (.branch 13 (.branch 12 (.leaf (22)) (.leaf (27))) (.branch 14 (.leaf (17)) (.leaf (6)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (9)) (.branch 17 (.leaf (13)) (.leaf (18)))) (.branch 20 (.branch 19 (.leaf (24)) (.leaf (30))) (.branch 21 (.leaf (19)) (.leaf (10))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (14)) (.leaf (20))) (.branch 25 (.leaf (15)) (.leaf (21)))) (.branch 28 (.branch 27 (.leaf (25)) (.leaf (31))) (.branch 29 (.leaf (35)) (.leaf (43))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (49)) (.branch 32 (.leaf (36)) (.leaf (23)))) (.branch 35 (.branch 34 (.leaf (28)) (.leaf (33))) (.branch 36 (.leaf (39)) (.leaf (46))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (52)) (.leaf (40))) (.branch 40 (.leaf (26)) (.leaf (32)))) (.branch 43 (.branch 42 (.leaf (37)) (.leaf (38))) (.branch 44 (.leaf (29)) (.leaf (34)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (41)) (.branch 47 (.leaf (42)) (.leaf (44)))) (.branch 50 (.branch 49 (.leaf (50)) (.leaf (54))) (.branch 51 (.leaf (58)) (.leaf (45))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (47)) (.leaf (53))) (.branch 55 (.leaf (56)) (.leaf (57)))) (.branch 58 (.branch 57 (.leaf (48)) (.leaf (51))) (.branch 59 (.leaf (55)) (.leaf (59))))))))
noncomputable def facesBack (p : Fin 60) : Fin 60 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 60, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 60 := by decide +kernel
theorem faces_partition : ∀ p : Fin 60, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [3,4,7,7,4,7,7,4,4,5,5,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 20 - 30 + 12 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 5 (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.leaf (⟨-1,1,-1,0⟩))) (.branch 6 (.leaf (⟨1,2,0,1⟩)) (.leaf (⟨-1,0,1,-1⟩))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩))) (.branch 10 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,0,2,1⟩)))) (.branch 13 (.branch 12 (.leaf (⟨0,1,-1,1⟩)) (.leaf (⟨1,1,1,2⟩))) (.branch 14 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨1,1,-2,-1⟩)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (⟨1,-1,2,-1⟩)) (.branch 17 (.leaf (⟨-1,-2,-1,-3⟩)) (.leaf (⟨1,-2,1,-1⟩)))) (.branch 20 (.branch 19 (.leaf (⟨-2,-3,-1,-2⟩)) (.leaf (⟨1,-1,-1,2⟩))) (.branch 21 (.leaf (⟨-1,-2,2,3⟩)) (.leaf (⟨-2,1,-3,1⟩))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (⟨1,3,1,4⟩)) (.leaf (⟨-3,2,-2,1⟩))) (.branch 25 (.leaf (⟨2,5,1,3⟩)) (.leaf (⟨-2,-1,-3,-2⟩)))) (.branch 28 (.branch 27 (.leaf (⟨4,1,3,1⟩)) (.leaf (⟨-1,3,-1,2⟩))) (.branch 29 (.leaf (⟨-3,-1,-2,-1⟩)) (.leaf (⟨3,1,-4,-1⟩))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (⟨-1,2,1,-3⟩)) (.branch 32 (.leaf (⟨-2,-1,3,1⟩)) (.leaf (⟨3,2,4,3⟩)))) (.branch 35 (.branch 34 (.leaf (⟨3,4,2,3⟩)) (.leaf (⟨5,3,3,2⟩))) (.branch 36 (.leaf (⟨2,3,-3,-4⟩)) (.leaf (⟨2,-3,3,-4⟩))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (⟨-3,-5,-4,-7⟩)) (.leaf (⟨4,-3,3,-2⟩))) (.branch 40 (.leaf (⟨-3,-7,-2,-5⟩)) (.leaf (⟨3,-5,2,-3⟩)))) (.branch 43 (.branch 42 (.leaf (⟨-5,-8,-3,-5⟩)) (.leaf (⟨3,-2,-4,3⟩))) (.branch 44 (.leaf (⟨-2,-5,3,7⟩)) (.leaf (⟨-7,-4,-5,-3⟩)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (⟨-7,3,-5,2⟩)) (.branch 47 (.leaf (⟨3,10,2,7⟩)) (.leaf (⟨-5,-3,7,4⟩)))) (.branch 50 (.branch 49 (.leaf (⟨-5,2,7,-3⟩)) (.leaf (⟨2,7,-3,-10⟩))) (.branch 51 (.leaf (⟨-5,-2,-7,-3⟩)) (.leaf (⟨11,3,7,2⟩))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (⟨-3,8,-2,5⟩)) (.leaf (⟨-8,-3,-5,-2⟩))) (.branch 55 (.leaf (⟨7,5,-10,-7⟩)) (.leaf (⟨10,7,7,5⟩)))) (.branch 58 (.branch 57 (.leaf (⟨8,11,5,7⟩)) (.leaf (⟨-8,-19,-5,-12⟩))) (.branch 59 (.leaf (⟨-19,-11,-12,-7⟩)) (.leaf (⟨11,-8,7,-5⟩))))))))
noncomputable def liftMatrix (p : Fin 60) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 60) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],10⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],11⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],12⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],13⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],14⟩,⟨⟨1,-1,2,-1⟩,[.t (0),.s,.t (-2),.s,.t (-1)],15⟩,⟨⟨-1,-2,-1,-3⟩,[.t (1),.s,.t (3)],16⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],17⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],18⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],19⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],20⟩,⟨⟨-2,1,-3,1⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-1)],21⟩,⟨⟨1,3,1,4⟩,[.t (1),.s,.t (4)],22⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],23⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],24⟩,⟨⟨-2,-1,-3,-2⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (0)],25⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],26⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],27⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],28⟩,⟨⟨3,1,-4,-1⟩,[.t (-1),.s,.t (-4),.s,.t (0)],29⟩,⟨⟨-1,2,1,-3⟩,[.t (-1),.s,.t (-3)],30⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],31⟩,⟨⟨3,2,4,3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],32⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],33⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],34⟩,⟨⟨2,3,-3,-4⟩,[.t (-1),.s,.t (-3),.s,.t (1)],35⟩,⟨⟨2,-3,3,-4⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2)],36⟩,⟨⟨-3,-5,-4,-7⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],37⟩,⟨⟨4,-3,3,-2⟩,[.t (1),.s,.t (-3),.s,.t (-1)],38⟩,⟨⟨-3,-7,-2,-5⟩,[.t (1),.s,.t (-2),.s,.t (2)],39⟩,⟨⟨3,-5,2,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2)],40⟩,⟨⟨-5,-8,-3,-5⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (1)],41⟩,⟨⟨3,-2,-4,3⟩,[.t (-1),.s,.t (-4),.s,.t (-1)],42⟩,⟨⟨-2,-5,3,7⟩,[.t (-1),.s,.t (-3),.s,.t (2)],43⟩,⟨⟨-7,-4,-5,-3⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (0)],44⟩,⟨⟨-7,3,-5,2⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-1)],45⟩,⟨⟨3,10,2,7⟩,[.t (1),.s,.t (-2),.s,.t (3)],46⟩,⟨⟨-5,-3,7,4⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (0)],47⟩,⟨⟨-5,2,7,-3⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-1)],48⟩,⟨⟨2,7,-3,-10⟩,[.t (-1),.s,.t (-3),.s,.t (3)],49⟩,⟨⟨-5,-2,-7,-3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],50⟩,⟨⟨11,3,7,2⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (0)],51⟩,⟨⟨-3,8,-2,5⟩,[.t (1),.s,.t (-2),.s,.t (-3)],52⟩,⟨⟨-8,-3,-5,-2⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (0)],53⟩,⟨⟨7,5,-10,-7⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (0)],54⟩,⟨⟨10,7,7,5⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],55⟩,⟨⟨8,11,5,7⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (1)],56⟩,⟨⟨-8,-19,-5,-12⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (2)],57⟩,⟨⟨-19,-11,-12,-7⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (0)],58⟩,⟨⟨11,-8,7,-5⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-1)],59⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 60 ∧ ((List.finRange 60).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 60) := [⟨9,1,⟨⟨-1,-3,0,-1⟩,[.t (3)],0⟩⟩,⟨29,5,⟨⟨13,11,7,6⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨47,7,⟨⟨67,49,41,30⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨54,10,⟨⟨213,151,134,95⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨49,9,⟨⟨35,24,51,35⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-7),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨20,3,⟨⟨-7,-4,-12,-7⟩,[.t (0),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,2,⟨⟨-1,0,-4,-1⟩,[.t (0),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨10,2,⟨⟨-1,0,4,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨25,3,⟨⟨-7,4,12,-7⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨50,9,⟨⟨35,-24,-51,35⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨37,6,⟨⟨56,-41,41,-30⟩,[.t (1),.s,.t (-3),.s,.t (-4),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨22,4,⟨⟨8,-7,7,-6⟩,[.t (1),.s,.t (-7),.s,.t (-1)],0⟩⟩,⟨26,4,⟨⟨-6,7,-7,8⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨44,6,⟨⟨-30,41,-41,56⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨55,11,⟨⟨-188,267,-119,169⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨46,8,⟨⟨43,-63,28,-41⟩,[.t (1),.s,.t (-2),.s,.t (-8),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨51,8,⟨⟨-41,63,-28,43⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨58,11,⟨⟨169,-267,119,-188⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨57,10,⟨⟨95,-151,-134,213⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨41,7,⟨⟨30,-49,-41,67⟩,[.t (-1),.s,.t (-4),.s,.t (-4),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨24,5,⟨⟨6,-11,-7,13⟩,[.t (-1),.s,.t (-7),.s,.t (-2)],0⟩⟩,⟨5,1,⟨⟨-1,3,0,-1⟩,[.t (-3)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-3,4),(-5,7),(-7,10),(-2,3),(-1,2),(0,1),(1,2),(2,3),(5,7),(3,4),(1,1),(4,3),(7,5),(10,7),(3,2),(11,7),(19,12),(8,5),(5,3),(2,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end A7_c8

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
