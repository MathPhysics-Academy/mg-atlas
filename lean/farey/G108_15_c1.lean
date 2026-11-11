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
namespace G108_15_c1
noncomputable def originalSData : LookupTree (Fin 108) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (9)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (12)) (.branch 8 (.leaf (0)) (.leaf (15)))) (.branch 11 (.branch 10 (.leaf (14)) (.leaf (18))) (.branch 12 (.leaf (10)) (.leaf (16)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (17)) (.branch 15 (.leaf (21)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (23)) (.leaf (24))) (.branch 19 (.leaf (22)) (.leaf (27))))) (.branch 23 (.branch 21 (.leaf (28)) (.branch 22 (.leaf (4)) (.leaf (11)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (30))) (.branch 26 (.leaf (32)) (.leaf (34))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (26)) (.branch 29 (.leaf (31)) (.leaf (36)))) (.branch 31 (.leaf (13)) (.branch 32 (.leaf (35)) (.leaf (38))))) (.branch 36 (.branch 34 (.leaf (40)) (.branch 35 (.leaf (19)) (.leaf (20)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (42))) (.branch 39 (.leaf (44)) (.leaf (46)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (45)) (.branch 42 (.leaf (49)) (.leaf (47)))) (.branch 45 (.branch 44 (.leaf (52)) (.leaf (25))) (.branch 46 (.leaf (53)) (.leaf (29))))) (.branch 50 (.branch 48 (.leaf (55)) (.branch 49 (.leaf (43)) (.leaf (54)))) (.branch 52 (.branch 51 (.leaf (59)) (.leaf (61))) (.branch 53 (.leaf (56)) (.leaf (33)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (64)) (.branch 56 (.leaf (37)) (.leaf (48)))) (.branch 58 (.leaf (67)) (.branch 59 (.leaf (62)) (.leaf (65))))) (.branch 63 (.branch 61 (.leaf (71)) (.branch 62 (.leaf (66)) (.leaf (72)))) (.branch 65 (.branch 64 (.leaf (73)) (.leaf (41))) (.branch 66 (.leaf (75)) (.leaf (77)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (63)) (.branch 69 (.leaf (79)) (.leaf (81)))) (.branch 72 (.branch 71 (.leaf (69)) (.leaf (76))) (.branch 73 (.leaf (78)) (.leaf (57))))) (.branch 77 (.branch 75 (.leaf (84)) (.branch 76 (.leaf (50)) (.leaf (82)))) (.branch 79 (.branch 78 (.leaf (51)) (.leaf (58))) (.branch 80 (.leaf (74)) (.leaf (87))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (83)) (.branch 83 (.leaf (60)) (.leaf (70)))) (.branch 85 (.leaf (68)) (.branch 86 (.leaf (90)) (.leaf (92))))) (.branch 90 (.branch 88 (.leaf (85)) (.branch 89 (.leaf (95)) (.leaf (97)))) (.branch 92 (.branch 91 (.leaf (80)) (.leaf (100))) (.branch 93 (.leaf (89)) (.leaf (99)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (93)) (.branch 96 (.leaf (91)) (.leaf (104)))) (.branch 99 (.branch 98 (.leaf (86)) (.leaf (94))) (.branch 100 (.leaf (98)) (.leaf (88))))) (.branch 104 (.branch 102 (.leaf (102)) (.branch 103 (.leaf (96)) (.leaf (106)))) (.branch 106 (.branch 105 (.leaf (101)) (.leaf (107))) (.branch 107 (.leaf (105)) (.leaf (103)))))))))
noncomputable def originalS (p : Fin 108) : Fin 108 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 108) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (10)) (.leaf (11))))) (.branch 9 (.branch 7 (.leaf (13)) (.branch 8 (.leaf (14)) (.leaf (16)))) (.branch 11 (.branch 10 (.leaf (17)) (.leaf (1))) (.branch 12 (.leaf (19)) (.leaf (20)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (22)) (.leaf (18)))) (.branch 18 (.branch 17 (.leaf (24)) (.leaf (25))) (.branch 19 (.leaf (26)) (.leaf (28))))) (.branch 23 (.branch 21 (.leaf (29)) (.branch 22 (.leaf (30)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (31)) (.leaf (3))) (.branch 26 (.leaf (33)) (.leaf (35))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (21)) (.branch 29 (.leaf (5)) (.leaf (37)))) (.branch 31 (.leaf (38)) (.branch 32 (.leaf (39)) (.leaf (12))))) (.branch 36 (.branch 34 (.leaf (41)) (.branch 35 (.leaf (9)) (.leaf (15)))) (.branch 38 (.branch 37 (.leaf (34)) (.leaf (43))) (.branch 39 (.leaf (45)) (.leaf (47)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (48)) (.branch 42 (.leaf (50)) (.leaf (51)))) (.branch 45 (.branch 44 (.leaf (32)) (.leaf (23))) (.branch 46 (.leaf (54)) (.leaf (27))))) (.branch 50 (.branch 48 (.leaf (56)) (.branch 49 (.leaf (57)) (.leaf (58)))) (.branch 52 (.branch 51 (.leaf (60)) (.leaf (62))) (.branch 53 (.leaf (63)) (.leaf (52)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (65)) (.branch 56 (.leaf (66)) (.leaf (44)))) (.branch 58 (.leaf (68)) (.branch 59 (.leaf (69)) (.leaf (70))))) (.branch 63 (.branch 61 (.leaf (59)) (.branch 62 (.leaf (36)) (.leaf (40)))) (.branch 65 (.branch 64 (.leaf (74)) (.leaf (72))) (.branch 66 (.leaf (76)) (.leaf (78)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (55)) (.branch 69 (.leaf (80)) (.leaf (49)))) (.branch 72 (.branch 71 (.leaf (61)) (.leaf (82))) (.branch 73 (.leaf (83)) (.leaf (42))))) (.branch 77 (.branch 75 (.leaf (85)) (.branch 76 (.leaf (81)) (.leaf (75)))) (.branch 79 (.branch 78 (.leaf (46)) (.leaf (53))) (.branch 80 (.leaf (86)) (.leaf (88))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (77)) (.branch 83 (.leaf (71)) (.leaf (64)))) (.branch 85 (.leaf (89)) (.branch 86 (.leaf (91)) (.leaf (93))))) (.branch 90 (.branch 88 (.leaf (94)) (.branch 89 (.leaf (96)) (.leaf (98)))) (.branch 92 (.branch 91 (.leaf (99)) (.leaf (101))) (.branch 93 (.leaf (67)) (.leaf (79)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (102)) (.branch 96 (.leaf (103)) (.leaf (97)))) (.branch 99 (.branch 98 (.leaf (73)) (.leaf (84))) (.branch 100 (.leaf (104)) (.leaf (105))))) (.branch 104 (.branch 102 (.leaf (92)) (.branch 103 (.leaf (106)) (.leaf (95)))) (.branch 106 (.branch 105 (.leaf (107)) (.leaf (100))) (.branch 107 (.leaf (87)) (.leaf (90)))))))))
noncomputable def originalT (p : Fin 108) : Fin 108 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 54) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (10)) (.branch 15 (.leaf (3)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (11))) (.branch 19 (.leaf (8)) (.leaf (12))))) (.branch 23 (.branch 21 (.leaf (13)) (.branch 22 (.leaf (6)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (9)) (.leaf (10))) (.branch 26 (.leaf (14)) (.leaf (12))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (15)) (.branch 29 (.leaf (16)) (.leaf (17)))) (.branch 31 (.leaf (11)) (.branch 32 (.leaf (13)) (.leaf (18))))) (.branch 36 (.branch 34 (.leaf (19)) (.branch 35 (.leaf (15)) (.leaf (16)))) (.branch 38 (.branch 37 (.leaf (20)) (.leaf (21))) (.branch 39 (.leaf (14)) (.leaf (17)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (22)) (.branch 42 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 44 (.leaf (25)) (.leaf (18))) (.branch 46 (.leaf (19)) (.leaf (20))))) (.branch 50 (.branch 48 (.leaf (21)) (.branch 49 (.leaf (26)) (.leaf (27)))) (.branch 52 (.branch 51 (.leaf (28)) (.leaf (29))) (.branch 53 (.leaf (26)) (.leaf (22)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (23)) (.branch 56 (.leaf (24)) (.leaf (25)))) (.branch 58 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32))))) (.branch 63 (.branch 61 (.leaf (33)) (.branch 62 (.leaf (34)) (.leaf (35)))) (.branch 65 (.branch 64 (.leaf (30)) (.leaf (27))) (.branch 66 (.leaf (28)) (.leaf (29)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (36)) (.branch 69 (.leaf (37)) (.leaf (38)))) (.branch 72 (.branch 71 (.leaf (39)) (.leaf (40))) (.branch 73 (.leaf (31)) (.leaf (36))))) (.branch 77 (.branch 75 (.leaf (37)) (.branch 76 (.leaf (32)) (.leaf (33)))) (.branch 79 (.branch 78 (.leaf (34)) (.leaf (35))) (.branch 80 (.leaf (41)) (.leaf (42))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (39)) (.branch 83 (.leaf (40)) (.leaf (38)))) (.branch 85 (.leaf (41)) (.branch 86 (.leaf (42)) (.leaf (43))))) (.branch 90 (.branch 88 (.leaf (44)) (.branch 89 (.leaf (45)) (.leaf (43)))) (.branch 92 (.branch 91 (.leaf (44)) (.leaf (45))) (.branch 93 (.leaf (46)) (.leaf (47)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (48)) (.branch 96 (.leaf (49)) (.leaf (50)))) (.branch 99 (.branch 98 (.leaf (46)) (.leaf (47))) (.branch 100 (.leaf (48)) (.leaf (49))))) (.branch 104 (.branch 102 (.leaf (50)) (.branch 103 (.leaf (51)) (.leaf (52)))) (.branch 106 (.branch 105 (.leaf (51)) (.leaf (52))) (.branch 107 (.leaf (53)) (.leaf (53)))))))))
noncomputable def projection (p : Fin 108) : Fin 54 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 108) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (11)))) (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (17)) (.leaf (19)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (20)) (.branch 15 (.leaf (25)) (.leaf (27)))) (.branch 18 (.branch 17 (.leaf (28)) (.leaf (29))) (.branch 19 (.leaf (32)) (.leaf (33))))) (.branch 23 (.branch 21 (.leaf (36)) (.branch 22 (.leaf (37)) (.leaf (40)))) (.branch 25 (.branch 24 (.leaf (41)) (.leaf (42))) (.branch 26 (.leaf (43)) (.leaf (48))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (49)) (.branch 29 (.leaf (50)) (.leaf (51)))) (.branch 31 (.leaf (57)) (.branch 32 (.leaf (58)) (.leaf (59))))) (.branch 36 (.branch 34 (.leaf (60)) (.branch 35 (.leaf (61)) (.leaf (62)))) (.branch 38 (.branch 37 (.leaf (67)) (.leaf (68))) (.branch 39 (.leaf (69)) (.leaf (70)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (71)) (.branch 42 (.leaf (79)) (.leaf (80)))) (.branch 45 (.branch 44 (.leaf (86)) (.leaf (87))) (.branch 46 (.leaf (88)) (.leaf (92))))) (.branch 50 (.branch 48 (.leaf (93)) (.branch 49 (.leaf (94)) (.leaf (95)))) (.branch 52 (.branch 51 (.leaf (96)) (.leaf (102))) (.branch 53 (.leaf (103)) (.leaf (106))))))))
noncomputable def representative (p : Fin 54) : Fin 108 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (11))) (.branch 12 (.leaf (10)) (.leaf (15)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (16)) (.branch 15 (.leaf (18)) (.leaf (12)))) (.branch 18 (.branch 17 (.leaf (13)) (.leaf (20))) (.branch 19 (.leaf (14)) (.leaf (22))))) (.branch 23 (.branch 21 (.leaf (17)) (.branch 22 (.leaf (24)) (.leaf (19)))) (.branch 25 (.branch 24 (.leaf (27)) (.leaf (21))) (.branch 26 (.leaf (26)) (.leaf (25))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (23)) (.branch 29 (.leaf (32)) (.leaf (34)))) (.branch 31 (.leaf (36)) (.branch 32 (.leaf (35)) (.leaf (28))))) (.branch 36 (.branch 34 (.leaf (40)) (.branch 35 (.leaf (29)) (.leaf (31)))) (.branch 38 (.branch 37 (.leaf (30)) (.leaf (41))) (.branch 39 (.leaf (39)) (.leaf (38)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (33)) (.branch 42 (.leaf (37)) (.leaf (44)))) (.branch 45 (.branch 44 (.leaf (46)) (.leaf (42))) (.branch 46 (.leaf (49)) (.leaf (43))))) (.branch 50 (.branch 48 (.leaf (48)) (.branch 49 (.leaf (47)) (.leaf (45)))) (.branch 52 (.branch 51 (.leaf (51)) (.leaf (50))) (.branch 53 (.leaf (53)) (.leaf (52))))))))
noncomputable def S (p : Fin 54) : Fin 54 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (8)) (.leaf (10))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (1)) (.leaf (12)))) (.branch 11 (.branch 10 (.leaf (13)) (.leaf (0))) (.branch 12 (.leaf (14)) (.leaf (16)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (17)) (.branch 15 (.leaf (19)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (4)) (.leaf (21))) (.branch 19 (.leaf (9)) (.leaf (23))))) (.branch 23 (.branch 21 (.leaf (15)) (.branch 22 (.leaf (25)) (.leaf (26)))) (.branch 25 (.branch 24 (.leaf (28)) (.leaf (29))) (.branch 26 (.leaf (18)) (.leaf (30))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (31)) (.branch 29 (.leaf (33)) (.leaf (35)))) (.branch 31 (.leaf (37)) (.branch 32 (.leaf (38)) (.leaf (39))))) (.branch 36 (.branch 34 (.leaf (32)) (.branch 35 (.leaf (20)) (.leaf (22)))) (.branch 38 (.branch 37 (.leaf (24)) (.leaf (42))) (.branch 39 (.leaf (27)) (.leaf (34)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (40)) (.branch 42 (.leaf (43)) (.leaf (45)))) (.branch 45 (.branch 44 (.leaf (47)) (.leaf (48))) (.branch 46 (.leaf (50)) (.leaf (36))))) (.branch 50 (.branch 48 (.leaf (41)) (.branch 49 (.leaf (51)) (.leaf (52)))) (.branch 52 (.branch 51 (.leaf (46)) (.leaf (53))) (.branch 53 (.leaf (49)) (.leaf (44))))))))
noncomputable def T (p : Fin 54) : Fin 54 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (10)) (.branch 2 (.leaf (7)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (16)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (15)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (18)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (8)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (9)) (.branch 15 (.leaf (11)) (.leaf (20)))) (.branch 18 (.branch 17 (.leaf (12)) (.leaf (13))) (.branch 19 (.leaf (25)) (.leaf (14))))) (.branch 23 (.branch 21 (.leaf (34)) (.branch 22 (.leaf (17)) (.leaf (35)))) (.branch 25 (.branch 24 (.leaf (19)) (.leaf (36))) (.branch 26 (.leaf (21)) (.leaf (22))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (38)) (.branch 29 (.leaf (23)) (.leaf (24)))) (.branch 31 (.leaf (26)) (.branch 32 (.leaf (27)) (.leaf (33))))) (.branch 36 (.branch 34 (.leaf (28)) (.branch 35 (.leaf (39)) (.leaf (29)))) (.branch 38 (.branch 37 (.leaf (46)) (.leaf (30))) (.branch 39 (.leaf (31)) (.leaf (32)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (40)) (.branch 42 (.leaf (47)) (.leaf (37)))) (.branch 45 (.branch 44 (.leaf (41)) (.leaf (53))) (.branch 46 (.leaf (42)) (.leaf (50))))) (.branch 50 (.branch 48 (.leaf (43)) (.branch 49 (.leaf (44)) (.leaf (52)))) (.branch 52 (.branch 51 (.leaf (45)) (.leaf (48))) (.branch 53 (.leaf (49)) (.leaf (51))))))))
noncomputable def Ti (p : Fin 54) : Fin 54 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 54) : Fin 54 := T (S p)
theorem quotient_relations : (∀ p : Fin 54, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 108, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 108, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 54, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 54)) := [[0,3,11],[1,2,8],[4,5,13],[6,7,12],[9,10,14],[15,16,17],[18,19,26],[20,21,29],[22,23,31],[24,25,30],[27,28,39],[32,33,40],[34,35,38],[36,37,43],[41,42,48],[44,45,52],[46,47,51],[49,50,53]]
noncomputable def verticesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (2)) (.leaf (11)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (14)) (.leaf (15)))) (.branch 18 (.branch 17 (.leaf (16)) (.leaf (17))) (.branch 19 (.leaf (18)) (.leaf (19))))) (.branch 23 (.branch 21 (.leaf (21)) (.branch 22 (.leaf (22)) (.leaf (24)))) (.branch 25 (.branch 24 (.leaf (25)) (.leaf (27))) (.branch 26 (.leaf (28)) (.leaf (20))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (30)) (.branch 29 (.leaf (31)) (.leaf (23)))) (.branch 31 (.leaf (29)) (.branch 32 (.leaf (26)) (.leaf (33))))) (.branch 36 (.branch 34 (.leaf (34)) (.branch 35 (.leaf (36)) (.leaf (37)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (40))) (.branch 39 (.leaf (38)) (.leaf (32)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (35)) (.branch 42 (.leaf (42)) (.leaf (43)))) (.branch 45 (.branch 44 (.leaf (41)) (.leaf (45))) (.branch 46 (.leaf (46)) (.leaf (48))))) (.branch 50 (.branch 48 (.leaf (49)) (.branch 49 (.leaf (44)) (.leaf (51)))) (.branch 52 (.branch 51 (.leaf (52)) (.leaf (50))) (.branch 53 (.leaf (47)) (.leaf (53))))))))
noncomputable def verticesIndex (p : Fin 54) : Fin 54 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (11)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (13)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (12)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (10)) (.branch 15 (.leaf (14)) (.leaf (15)))) (.branch 18 (.branch 17 (.leaf (16)) (.leaf (17))) (.branch 19 (.leaf (18)) (.leaf (19))))) (.branch 23 (.branch 21 (.leaf (26)) (.branch 22 (.leaf (20)) (.leaf (21)))) (.branch 25 (.branch 24 (.leaf (29)) (.leaf (22))) (.branch 26 (.leaf (23)) (.leaf (31))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (24)) (.branch 29 (.leaf (25)) (.leaf (30)))) (.branch 31 (.leaf (27)) (.branch 32 (.leaf (28)) (.leaf (39))))) (.branch 36 (.branch 34 (.leaf (32)) (.branch 35 (.leaf (33)) (.leaf (40)))) (.branch 38 (.branch 37 (.leaf (34)) (.leaf (35))) (.branch 39 (.leaf (38)) (.leaf (36)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (37)) (.branch 42 (.leaf (43)) (.leaf (41)))) (.branch 45 (.branch 44 (.leaf (42)) (.leaf (48))) (.branch 46 (.leaf (44)) (.leaf (45))))) (.branch 50 (.branch 48 (.leaf (52)) (.branch 49 (.leaf (46)) (.leaf (47)))) (.branch 52 (.branch 51 (.leaf (51)) (.leaf (49))) (.branch 53 (.leaf (50)) (.leaf (53))))))))
noncomputable def verticesBack (p : Fin 54) : Fin 54 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 54, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 54 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 54, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 54)) := [[0,1],[2,4],[3,6],[5,9],[7,8],[10,11],[12,15],[13,16],[14,18],[17,20],[19,22],[21,24],[23,27],[25,26],[28,32],[29,34],[30,36],[31,35],[33,40],[37,41],[38,39],[42,44],[43,46],[45,49],[47,48],[50,51],[52,53]]
noncomputable def edgesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (9)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (10))) (.branch 12 (.leaf (11)) (.leaf (12)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (14)) (.branch 15 (.leaf (16)) (.leaf (13)))) (.branch 18 (.branch 17 (.leaf (15)) (.leaf (18))) (.branch 19 (.leaf (17)) (.leaf (20))))) (.branch 23 (.branch 21 (.leaf (19)) (.branch 22 (.leaf (22)) (.leaf (21)))) (.branch 25 (.branch 24 (.leaf (24)) (.leaf (23))) (.branch 26 (.leaf (26)) (.leaf (27))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (25)) (.branch 29 (.leaf (28)) (.leaf (30)))) (.branch 31 (.leaf (32)) (.branch 32 (.leaf (34)) (.leaf (29))))) (.branch 36 (.branch 34 (.leaf (36)) (.branch 35 (.leaf (31)) (.leaf (35)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (38))) (.branch 39 (.leaf (40)) (.leaf (41)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (37)) (.branch 42 (.leaf (39)) (.leaf (42)))) (.branch 45 (.branch 44 (.leaf (44)) (.leaf (43))) (.branch 46 (.leaf (46)) (.leaf (45))))) (.branch 50 (.branch 48 (.leaf (48)) (.branch 49 (.leaf (49)) (.leaf (47)))) (.branch 52 (.branch 51 (.leaf (50)) (.leaf (51))) (.branch 53 (.leaf (52)) (.leaf (53))))))))
noncomputable def edgesIndex (p : Fin 54) : Fin 54 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (10))) (.branch 12 (.leaf (11)) (.leaf (12)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (15)) (.branch 15 (.leaf (13)) (.leaf (16)))) (.branch 18 (.branch 17 (.leaf (14)) (.leaf (18))) (.branch 19 (.leaf (17)) (.leaf (20))))) (.branch 23 (.branch 21 (.leaf (19)) (.branch 22 (.leaf (22)) (.leaf (21)))) (.branch 25 (.branch 24 (.leaf (24)) (.leaf (23))) (.branch 26 (.leaf (27)) (.leaf (25))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (26)) (.branch 29 (.leaf (28)) (.leaf (32)))) (.branch 31 (.leaf (29)) (.branch 32 (.leaf (34)) (.leaf (30))))) (.branch 36 (.branch 34 (.leaf (36)) (.branch 35 (.leaf (31)) (.leaf (35)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (40))) (.branch 39 (.leaf (37)) (.leaf (41)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (38)) (.branch 42 (.leaf (39)) (.leaf (42)))) (.branch 45 (.branch 44 (.leaf (44)) (.leaf (43))) (.branch 46 (.leaf (46)) (.leaf (45))))) (.branch 50 (.branch 48 (.leaf (49)) (.branch 49 (.leaf (47)) (.leaf (48)))) (.branch 52 (.branch 51 (.leaf (50)) (.leaf (51))) (.branch 53 (.leaf (52)) (.leaf (53))))))))
noncomputable def edgesBack (p : Fin 54) : Fin 54 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 54, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 54 := by decide +kernel
theorem edges_partition : ∀ p : Fin 54, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 54)) := [[0,2,5,10],[1,3,7],[4,8,12,16],[6,11,14,19,23,28,33,32,39,34,20,15],[9,13,17,21,25,18],[22,26,30,37,42,45,50,46,36,24,29,35],[27,31,38],[40],[41,43,47],[44,48,51,53],[49,52]]
noncomputable def facesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (7)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (6)) (.leaf (8)))) (.branch 11 (.branch 10 (.leaf (23)) (.leaf (3))) (.branch 12 (.leaf (12)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (24)) (.branch 15 (.leaf (13)) (.leaf (22)))) (.branch 18 (.branch 17 (.leaf (10)) (.leaf (25))) (.branch 19 (.leaf (28)) (.leaf (14))))) (.branch 23 (.branch 21 (.leaf (21)) (.branch 22 (.leaf (26)) (.leaf (29)))) (.branch 25 (.branch 24 (.leaf (15)) (.leaf (38))) (.branch 26 (.leaf (27)) (.leaf (30))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (41)) (.branch 29 (.leaf (16)) (.leaf (39)))) (.branch 31 (.leaf (31)) (.branch 32 (.leaf (42)) (.leaf (18))))) (.branch 36 (.branch 34 (.leaf (17)) (.branch 35 (.leaf (20)) (.leaf (40)))) (.branch 38 (.branch 37 (.leaf (37)) (.leaf (32))) (.branch 39 (.leaf (43)) (.leaf (19)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (44)) (.branch 42 (.leaf (45)) (.leaf (33)))) (.branch 45 (.branch 44 (.leaf (46)) (.leaf (48))) (.branch 46 (.leaf (34)) (.leaf (36))))) (.branch 50 (.branch 48 (.leaf (47)) (.branch 49 (.leaf (49)) (.leaf (52)))) (.branch 52 (.branch 51 (.leaf (35)) (.leaf (50))) (.branch 53 (.leaf (53)) (.leaf (51))))))))
noncomputable def facesIndex (p : Fin 54) : Fin 54 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (10)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (4)) (.leaf (8)))) (.branch 11 (.branch 10 (.leaf (12)) (.leaf (16))) (.branch 12 (.leaf (6)) (.leaf (11)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (14)) (.branch 15 (.leaf (19)) (.leaf (23)))) (.branch 18 (.branch 17 (.leaf (28)) (.leaf (33))) (.branch 19 (.leaf (32)) (.leaf (39))))) (.branch 23 (.branch 21 (.leaf (34)) (.branch 22 (.leaf (20)) (.leaf (15)))) (.branch 25 (.branch 24 (.leaf (9)) (.leaf (13))) (.branch 26 (.leaf (17)) (.leaf (21))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (25)) (.branch 29 (.leaf (18)) (.leaf (22)))) (.branch 31 (.leaf (26)) (.branch 32 (.leaf (30)) (.leaf (37))))) (.branch 36 (.branch 34 (.leaf (42)) (.branch 35 (.leaf (45)) (.leaf (50)))) (.branch 38 (.branch 37 (.leaf (46)) (.leaf (36))) (.branch 39 (.leaf (24)) (.leaf (29)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (35)) (.branch 42 (.leaf (27)) (.leaf (31)))) (.branch 45 (.branch 44 (.leaf (38)) (.leaf (40))) (.branch 46 (.leaf (41)) (.leaf (43))))) (.branch 50 (.branch 48 (.leaf (47)) (.branch 49 (.leaf (44)) (.leaf (48)))) (.branch 52 (.branch 51 (.leaf (51)) (.leaf (53))) (.branch 53 (.leaf (49)) (.leaf (52))))))))
noncomputable def facesBack (p : Fin 54) : Fin 54 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 54, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 54 := by decide +kernel
theorem faces_partition : ∀ p : Fin 54, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [4,3,4,12,6,12,3,1,3,4,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 18 - 27 + 11 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))) (.branch 11 (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.leaf (⟨-1,-3,0,-1⟩))) (.branch 12 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,1,-2,-1⟩)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (⟨2,1,1,1⟩)) (.branch 15 (.leaf (⟨-3,-2,-1,-1⟩)) (.leaf (⟨-3,-1,-2,-1⟩)))) (.branch 18 (.branch 17 (.leaf (⟨1,-2,1,-1⟩)) (.leaf (⟨-2,-3,-1,-2⟩))) (.branch 19 (.leaf (⟨-2,3,-1,1⟩)) (.leaf (⟨3,5,1,2⟩))))) (.branch 23 (.branch 21 (.leaf (⟨-3,2,-2,1⟩)) (.branch 22 (.leaf (⟨2,5,1,3⟩)) (.leaf (⟨5,-3,2,-1⟩)))) (.branch 25 (.branch 24 (.leaf (⟨-3,-8,-1,-3⟩)) (.leaf (⟨-7,-2,-3,-1⟩))) (.branch 26 (.leaf (⟨2,-5,1,-2⟩)) (.leaf (⟨5,2,2,1⟩))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (⟨-8,3,-3,1⟩)) (.branch 29 (.leaf (⟨3,11,1,4⟩)) (.leaf (⟨5,3,3,2⟩)))) (.branch 31 (.leaf (⟨-5,-7,-2,-3⟩)) (.branch 32 (.leaf (⟨-8,-5,-3,-2⟩)) (.leaf (⟨11,-3,4,-1⟩))))) (.branch 36 (.branch 34 (.leaf (⟨-3,-14,-1,-5⟩)) (.branch 35 (.leaf (⟨3,-5,2,-3⟩)) (.leaf (⟨-5,-8,-3,-5⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-7,5,-3,2⟩)) (.leaf (⟨5,12,2,5⟩))) (.branch 39 (.leaf (⟨-8,-3,-5,-2⟩)) (.leaf (⟨11,8,4,3⟩)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (⟨-14,-11,-5,-4⟩)) (.branch 42 (.leaf (⟨12,-5,5,-2⟩)) (.leaf (⟨-5,-17,-2,-7⟩)))) (.branch 45 (.branch 44 (.leaf (⟨12,7,5,3⟩)) (.leaf (⟨-17,5,-7,2⟩))) (.branch 46 (.leaf (⟨5,22,2,9⟩)) (.leaf (⟨7,-12,3,-5⟩))))) (.branch 50 (.branch 48 (.leaf (⟨-12,-19,-5,-8⟩)) (.branch 49 (.leaf (⟨-17,-12,-7,-5⟩)) (.leaf (⟨26,7,11,3⟩)))) (.branch 52 (.branch 51 (.leaf (⟨-7,19,-3,8⟩)) (.leaf (⟨-19,-7,-8,-3⟩))) (.branch 53 (.leaf (⟨22,17,9,7⟩)) (.leaf (⟨19,26,8,11⟩))))))))
noncomputable def liftMatrix (p : Fin 54) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 54) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],13⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],14⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],15⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],16⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],17⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],18⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],19⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],20⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],21⟩,⟨⟨5,-3,2,-1⟩,[.t (2),.s,.t (-2),.s,.t (-1)],22⟩,⟨⟨-3,-8,-1,-3⟩,[.t (3),.s,.t (3)],23⟩,⟨⟨-7,-2,-3,-1⟩,[.t (2),.s,.t (-3),.s,.t (0)],24⟩,⟨⟨2,-5,1,-2⟩,[.t (2),.s,.t (-2)],25⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],26⟩,⟨⟨-8,3,-3,1⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],27⟩,⟨⟨3,11,1,4⟩,[.t (3),.s,.t (4)],28⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],29⟩,⟨⟨-5,-7,-2,-3⟩,[.t (2),.s,.t (-2),.s,.t (1)],30⟩,⟨⟨-8,-5,-3,-2⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (0)],31⟩,⟨⟨11,-3,4,-1⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],32⟩,⟨⟨-3,-14,-1,-5⟩,[.t (3),.s,.t (5)],33⟩,⟨⟨3,-5,2,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2)],34⟩,⟨⟨-5,-8,-3,-5⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (1)],35⟩,⟨⟨-7,5,-3,2⟩,[.t (2),.s,.t (-3),.s,.t (-1)],36⟩,⟨⟨5,12,2,5⟩,[.t (2),.s,.t (-2),.s,.t (2)],37⟩,⟨⟨-8,-3,-5,-2⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (0)],38⟩,⟨⟨11,8,4,3⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],39⟩,⟨⟨-14,-11,-5,-4⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],40⟩,⟨⟨12,-5,5,-2⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],41⟩,⟨⟨-5,-17,-2,-7⟩,[.t (2),.s,.t (-2),.s,.t (3)],42⟩,⟨⟨12,7,5,3⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (0)],43⟩,⟨⟨-17,5,-7,2⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-1)],44⟩,⟨⟨5,22,2,9⟩,[.t (2),.s,.t (-2),.s,.t (4)],45⟩,⟨⟨7,-12,3,-5⟩,[.t (2),.s,.t (-3),.s,.t (-2)],46⟩,⟨⟨-12,-19,-5,-8⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (1)],47⟩,⟨⟨-17,-12,-7,-5⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],48⟩,⟨⟨26,7,11,3⟩,[.t (2),.s,.t (-3),.s,.t (-4),.s,.t (0)],49⟩,⟨⟨-7,19,-3,8⟩,[.t (2),.s,.t (-3),.s,.t (-3)],50⟩,⟨⟨-19,-7,-8,-3⟩,[.t (2),.s,.t (-3),.s,.t (-3),.s,.t (0)],51⟩,⟨⟨22,17,9,7⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],52⟩,⟨⟨19,26,8,11⟩,[.t (2),.s,.t (-3),.s,.t (-3),.s,.t (1)],53⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 54 ∧ ((List.finRange 54).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 54) := [⟨11,2,⟨⟨1,4,0,1⟩,[.t (4)],0⟩⟩,⟨12,3,⟨⟨7,4,5,3⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,1,⟨⟨1,0,3,1⟩,[.t (0),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨8,1,⟨⟨1,0,-3,1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨15,3,⟨⟨3,-4,-5,7⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨38,7,⟨⟨-71,112,-26,41⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨35,5,⟨⟨-49,80,-19,31⟩,[.t (2),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨21,4,⟨⟨-13,24,-6,11⟩,[.t (2),.s,.t (-6),.s,.t (-2)],0⟩⟩,⟨24,4,⟨⟨11,-24,6,-13⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨49,8,⟨⟨-121,284,-49,115⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨53,10,⟨⟨-363,860,-149,353⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨47,9,⟨⟨181,-432,75,-179⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨48,9,⟨⟨-179,432,-75,181⟩,[.t (2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨52,10,⟨⟨353,-860,149,-363⟩,[.t (2),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨45,8,⟨⟨115,-284,49,-121⟩,[.t (2),.s,.t (-3),.s,.t (-9),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨31,5,⟨⟨31,-80,19,-49⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨39,7,⟨⟨41,-112,26,-71⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨40,6,⟨⟨-71,196,-25,69⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-3)],0⟩⟩,⟨33,6,⟨⟨69,-196,25,-71⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-7),.s,.t (-3)],0⟩⟩,⟨10,2,⟨⟨1,-4,0,1⟩,[.t (-4)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-1,2),(0,1),(1,1),(3,2),(8,5),(5,3),(2,1),(7,3),(26,11),(19,8),(12,5),(17,7),(22,9),(5,2),(8,3),(11,4),(14,5),(3,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G108_15_c1

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
