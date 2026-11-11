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
namespace PSL2_17_c1
noncomputable def originalSData : LookupTree (Fin 108) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (0)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (10)) (.leaf (11)))) (.branch 11 (.branch 10 (.leaf (13)) (.leaf (2))) (.branch 12 (.leaf (15)) (.leaf (17)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (16)) (.branch 15 (.leaf (20)) (.leaf (6)))) (.branch 18 (.branch 17 (.leaf (23)) (.leaf (22))) (.branch 19 (.leaf (25)) (.leaf (27))))) (.branch 23 (.branch 21 (.leaf (24)) (.branch 22 (.leaf (30)) (.leaf (31)))) (.branch 25 (.branch 24 (.leaf (9)) (.leaf (34))) (.branch 26 (.leaf (32)) (.leaf (36))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (33)) (.branch 29 (.leaf (38)) (.leaf (39)))) (.branch 31 (.leaf (35)) (.branch 32 (.leaf (12)) (.leaf (42))))) (.branch 36 (.branch 34 (.leaf (44)) (.branch 35 (.leaf (14)) (.leaf (47)))) (.branch 38 (.branch 37 (.leaf (43)) (.leaf (49))) (.branch 39 (.leaf (45)) (.leaf (46)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (52)) (.branch 42 (.leaf (54)) (.leaf (18)))) (.branch 45 (.branch 44 (.leaf (56)) (.leaf (19))) (.branch 46 (.leaf (58)) (.leaf (59))))) (.branch 50 (.branch 48 (.leaf (21)) (.branch 49 (.leaf (55)) (.leaf (57)))) (.branch 52 (.branch 51 (.leaf (64)) (.leaf (66))) (.branch 53 (.leaf (60)) (.leaf (65)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (61)) (.branch 56 (.leaf (69)) (.leaf (26)))) (.branch 58 (.leaf (70)) (.branch 59 (.leaf (28)) (.leaf (29))))) (.branch 63 (.branch 61 (.leaf (67)) (.branch 62 (.leaf (74)) (.leaf (76)))) (.branch 65 (.branch 64 (.leaf (62)) (.leaf (71))) (.branch 66 (.leaf (73)) (.leaf (72)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (40)) (.branch 69 (.leaf (78)) (.leaf (75)))) (.branch 72 (.branch 71 (.leaf (37)) (.leaf (81))) (.branch 73 (.leaf (83)) (.leaf (82))))) (.branch 77 (.branch 75 (.leaf (41)) (.branch 76 (.leaf (48)) (.leaf (80)))) (.branch 79 (.branch 78 (.leaf (79)) (.leaf (84))) (.branch 80 (.leaf (86)) (.leaf (63))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (50)) (.branch 83 (.leaf (53)) (.leaf (51)))) (.branch 85 (.leaf (87)) (.branch 86 (.leaf (89)) (.leaf (88))))) (.branch 90 (.branch 88 (.leaf (68)) (.branch 89 (.leaf (77)) (.leaf (91)))) (.branch 92 (.branch 91 (.leaf (92)) (.leaf (94))) (.branch 93 (.leaf (95)) (.leaf (97)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (85)) (.branch 96 (.leaf (99)) (.leaf (98)))) (.branch 99 (.branch 98 (.leaf (100)) (.leaf (103))) (.branch 100 (.leaf (90)) (.leaf (104))))) (.branch 104 (.branch 102 (.leaf (106)) (.branch 103 (.leaf (101)) (.leaf (105)))) (.branch 106 (.branch 105 (.leaf (93)) (.leaf (96))) (.branch 107 (.leaf (107)) (.leaf (102)))))))))
noncomputable def originalS (p : Fin 108) : Fin 108 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 108) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (12)))) (.branch 11 (.branch 10 (.leaf (14)) (.leaf (0))) (.branch 12 (.leaf (16)) (.leaf (18)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (19)) (.branch 15 (.leaf (21)) (.leaf (22)))) (.branch 18 (.branch 17 (.leaf (24)) (.leaf (5))) (.branch 19 (.leaf (26)) (.leaf (28))))) (.branch 23 (.branch 21 (.leaf (29)) (.branch 22 (.leaf (31)) (.leaf (32)))) (.branch 25 (.branch 24 (.leaf (33)) (.leaf (35))) (.branch 26 (.leaf (30)) (.leaf (37))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (8)) (.branch 29 (.leaf (39)) (.leaf (40)))) (.branch 31 (.leaf (41)) (.branch 32 (.leaf (10)) (.leaf (43))))) (.branch 36 (.branch 34 (.leaf (45)) (.branch 35 (.leaf (46)) (.leaf (17)))) (.branch 38 (.branch 37 (.leaf (48)) (.leaf (50))) (.branch 39 (.leaf (51)) (.leaf (13)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (53)) (.branch 42 (.leaf (55)) (.leaf (47)))) (.branch 45 (.branch 44 (.leaf (57)) (.leaf (15))) (.branch 46 (.leaf (59)) (.leaf (60))))) (.branch 50 (.branch 48 (.leaf (61)) (.branch 49 (.leaf (62)) (.leaf (63)))) (.branch 52 (.branch 51 (.leaf (65)) (.leaf (67))) (.branch 53 (.leaf (58)) (.leaf (68)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (20)) (.branch 56 (.leaf (25)) (.leaf (69)))) (.branch 58 (.leaf (71)) (.branch 59 (.leaf (72)) (.leaf (23))))) (.branch 63 (.branch 61 (.leaf (73)) (.branch 62 (.leaf (75)) (.leaf (36)))) (.branch 65 (.branch 64 (.leaf (54)) (.leaf (77))) (.branch 66 (.leaf (66)) (.leaf (27)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (38)) (.branch 69 (.leaf (79)) (.leaf (80)))) (.branch 72 (.branch 71 (.leaf (76)) (.leaf (82))) (.branch 73 (.leaf (52)) (.leaf (84))))) (.branch 77 (.branch 75 (.leaf (34)) (.branch 76 (.leaf (42)) (.leaf (74)))) (.branch 79 (.branch 78 (.leaf (85)) (.leaf (81))) (.branch 80 (.leaf (49)) (.leaf (56))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (86)) (.branch 83 (.leaf (83)) (.leaf (44)))) (.branch 85 (.leaf (88)) (.branch 86 (.leaf (90)) (.leaf (91))))) (.branch 90 (.branch 88 (.leaf (64)) (.branch 89 (.leaf (70)) (.leaf (87)))) (.branch 92 (.branch 91 (.leaf (93)) (.leaf (95))) (.branch 93 (.leaf (96)) (.leaf (98)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (78)) (.branch 96 (.leaf (100)) (.leaf (101)))) (.branch 99 (.branch 98 (.leaf (102)) (.leaf (89))) (.branch 100 (.leaf (103)) (.leaf (105))))) (.branch 104 (.branch 102 (.leaf (92)) (.branch 103 (.leaf (97)) (.leaf (107)))) (.branch 106 (.branch 105 (.leaf (106)) (.leaf (94))) (.branch 107 (.leaf (104)) (.leaf (99)))))))))
noncomputable def originalT (p : Fin 108) : Fin 108 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 54) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (2)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (3))) (.branch 12 (.leaf (4)) (.leaf (7)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (9)) (.leaf (5)))) (.branch 18 (.branch 17 (.leaf (6)) (.leaf (10))) (.branch 19 (.leaf (11)) (.leaf (12))))) (.branch 23 (.branch 21 (.leaf (13)) (.branch 22 (.leaf (14)) (.leaf (7)))) (.branch 25 (.branch 24 (.leaf (8)) (.leaf (9))) (.branch 26 (.leaf (15)) (.leaf (16))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (17)) (.branch 29 (.leaf (18)) (.leaf (19)))) (.branch 31 (.leaf (20)) (.branch 32 (.leaf (10)) (.leaf (11))))) (.branch 36 (.branch 34 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 38 (.branch 37 (.leaf (21)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (25)) (.branch 42 (.leaf (26)) (.leaf (15)))) (.branch 45 (.branch 44 (.leaf (16)) (.leaf (17))) (.branch 46 (.leaf (18)) (.leaf (19))))) (.branch 50 (.branch 48 (.leaf (20)) (.branch 49 (.leaf (27)) (.leaf (28)))) (.branch 52 (.branch 51 (.leaf (29)) (.leaf (30))) (.branch 53 (.leaf (31)) (.leaf (32)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (33)) (.branch 56 (.leaf (34)) (.leaf (21)))) (.branch 58 (.leaf (22)) (.branch 59 (.leaf (23)) (.leaf (24))))) (.branch 63 (.branch 61 (.leaf (25)) (.branch 62 (.leaf (26)) (.leaf (35)))) (.branch 65 (.branch 64 (.leaf (36)) (.leaf (37))) (.branch 66 (.leaf (38)) (.leaf (39)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (31)) (.branch 69 (.leaf (40)) (.leaf (27)))) (.branch 72 (.branch 71 (.leaf (28)) (.leaf (29))) (.branch 73 (.leaf (30)) (.leaf (32))))) (.branch 77 (.branch 75 (.leaf (33)) (.branch 76 (.leaf (34)) (.leaf (36)))) (.branch 79 (.branch 78 (.leaf (41)) (.leaf (42))) (.branch 80 (.leaf (43)) (.leaf (35))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (37)) (.branch 83 (.leaf (38)) (.leaf (39)))) (.branch 85 (.leaf (40)) (.branch 86 (.leaf (44)) (.leaf (41))))) (.branch 90 (.branch 88 (.leaf (42)) (.branch 89 (.leaf (43)) (.leaf (45)))) (.branch 92 (.branch 91 (.leaf (46)) (.leaf (44))) (.branch 93 (.leaf (47)) (.leaf (48)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (45)) (.branch 96 (.leaf (46)) (.leaf (49)))) (.branch 99 (.branch 98 (.leaf (50)) (.leaf (51))) (.branch 100 (.leaf (47)) (.leaf (48))))) (.branch 104 (.branch 102 (.leaf (52)) (.branch 103 (.leaf (53)) (.leaf (49)))) (.branch 106 (.branch 105 (.leaf (50)) (.leaf (51))) (.branch 107 (.leaf (53)) (.leaf (52)))))))))
noncomputable def projection (p : Fin 108) : Fin 54 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 108) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (6)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (12)) (.leaf (13)))) (.branch 11 (.branch 10 (.leaf (14)) (.leaf (17))) (.branch 12 (.leaf (18)) (.leaf (19)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (20)) (.branch 15 (.leaf (21)) (.leaf (25)))) (.branch 18 (.branch 17 (.leaf (26)) (.leaf (27))) (.branch 19 (.leaf (28)) (.leaf (29))))) (.branch 23 (.branch 21 (.leaf (30)) (.branch 22 (.leaf (36)) (.leaf (37)))) (.branch 25 (.branch 24 (.leaf (38)) (.leaf (39))) (.branch 26 (.leaf (40)) (.leaf (41))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (48)) (.branch 29 (.leaf (49)) (.leaf (50)))) (.branch 31 (.leaf (51)) (.branch 32 (.leaf (52)) (.leaf (53))))) (.branch 36 (.branch 34 (.leaf (54)) (.branch 35 (.leaf (55)) (.leaf (62)))) (.branch 38 (.branch 37 (.leaf (63)) (.leaf (64))) (.branch 39 (.leaf (65)) (.leaf (66)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (68)) (.branch 42 (.leaf (77)) (.leaf (78)))) (.branch 45 (.branch 44 (.leaf (79)) (.leaf (85))) (.branch 46 (.leaf (89)) (.leaf (90))))) (.branch 50 (.branch 48 (.leaf (92)) (.branch 49 (.leaf (93)) (.leaf (96)))) (.branch 52 (.branch 51 (.leaf (97)) (.leaf (98))) (.branch 53 (.leaf (101)) (.leaf (102))))))))
noncomputable def representative (p : Fin 54) : Fin 108 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (3)))) (.branch 4 (.leaf (2)) (.branch 5 (.leaf (5)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (10)) (.leaf (6)))) (.branch 11 (.branch 10 (.leaf (13)) (.leaf (7))) (.branch 12 (.leaf (15)) (.leaf (17)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (9)) (.branch 15 (.leaf (20)) (.leaf (11)))) (.branch 18 (.branch 17 (.leaf (21)) (.leaf (12))) (.branch 19 (.leaf (23)) (.leaf (24))))) (.branch 23 (.branch 21 (.leaf (14)) (.branch 22 (.leaf (16)) (.leaf (28)))) (.branch 25 (.branch 24 (.leaf (18)) (.leaf (19))) (.branch 26 (.leaf (31)) (.leaf (33))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (34)) (.branch 29 (.leaf (22)) (.leaf (37)))) (.branch 31 (.leaf (39)) (.branch 32 (.leaf (25)) (.leaf (38))))) (.branch 36 (.branch 34 (.leaf (26)) (.branch 35 (.leaf (27)) (.leaf (36)))) (.branch 38 (.branch 37 (.leaf (35)) (.leaf (29))) (.branch 39 (.leaf (32)) (.leaf (30)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (42)) (.branch 42 (.leaf (43)) (.leaf (40)))) (.branch 45 (.branch 44 (.leaf (41)) (.leaf (45))) (.branch 46 (.leaf (44)) (.leaf (47))))) (.branch 50 (.branch 48 (.leaf (46)) (.branch 49 (.leaf (50)) (.leaf (51)))) (.branch 52 (.branch 51 (.leaf (48)) (.leaf (49))) (.branch 53 (.leaf (53)) (.leaf (52))))))))
noncomputable def S (p : Fin 54) : Fin 54 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (1)) (.leaf (4)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (12)))) (.branch 11 (.branch 10 (.leaf (14)) (.leaf (3))) (.branch 12 (.leaf (16)) (.leaf (18)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (19)) (.branch 15 (.leaf (10)) (.leaf (20)))) (.branch 18 (.branch 17 (.leaf (22)) (.leaf (5))) (.branch 19 (.leaf (24)) (.leaf (25))))) (.branch 23 (.branch 21 (.leaf (26)) (.branch 22 (.leaf (27)) (.leaf (29)))) (.branch 25 (.branch 24 (.leaf (30)) (.leaf (8))) (.branch 26 (.leaf (32)) (.leaf (34))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (35)) (.branch 29 (.leaf (36)) (.leaf (38)))) (.branch 31 (.leaf (31)) (.branch 32 (.leaf (23)) (.leaf (40))))) (.branch 36 (.branch 34 (.leaf (13)) (.branch 35 (.leaf (15)) (.leaf (21)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (41))) (.branch 39 (.leaf (39)) (.leaf (17)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (43)) (.branch 42 (.leaf (44)) (.leaf (37)))) (.branch 45 (.branch 44 (.leaf (28)) (.leaf (46))) (.branch 46 (.leaf (42)) (.leaf (48))))) (.branch 50 (.branch 48 (.leaf (49)) (.branch 49 (.leaf (51)) (.leaf (52)))) (.branch 52 (.branch 51 (.leaf (53)) (.leaf (45))) (.branch 53 (.leaf (47)) (.leaf (50))))))))
noncomputable def T (p : Fin 54) : Fin 54 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (3)) (.branch 2 (.leaf (1)) (.leaf (0)))) (.branch 4 (.leaf (10)) (.branch 5 (.leaf (2)) (.leaf (17))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (24)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (14))) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (33)) (.branch 15 (.leaf (9)) (.leaf (34)))) (.branch 18 (.branch 17 (.leaf (11)) (.leaf (39))) (.branch 19 (.leaf (12)) (.leaf (13))))) (.branch 23 (.branch 21 (.leaf (15)) (.branch 22 (.leaf (35)) (.leaf (16)))) (.branch 25 (.branch 24 (.leaf (31)) (.leaf (18))) (.branch 26 (.leaf (19)) (.leaf (20))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (21)) (.branch 29 (.leaf (43)) (.leaf (22)))) (.branch 31 (.leaf (23)) (.branch 32 (.leaf (30)) (.leaf (25))))) (.branch 36 (.branch 34 (.leaf (36)) (.branch 35 (.leaf (26)) (.leaf (27)))) (.branch 38 (.branch 37 (.leaf (28)) (.leaf (42))) (.branch 39 (.leaf (29)) (.leaf (38)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (32)) (.branch 42 (.leaf (37)) (.leaf (45)))) (.branch 45 (.branch 44 (.leaf (40)) (.leaf (41))) (.branch 46 (.leaf (51)) (.leaf (44))))) (.branch 50 (.branch 48 (.leaf (52)) (.branch 49 (.leaf (46)) (.leaf (47)))) (.branch 52 (.branch 51 (.leaf (53)) (.leaf (48))) (.branch 53 (.leaf (49)) (.leaf (50))))))))
noncomputable def Ti (p : Fin 54) : Fin 54 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 54) : Fin 54 := T (S p)
theorem quotient_relations : (∀ p : Fin 54, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 108, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 108, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 54, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 54)) := [[0,1,2],[3,4,7],[5,6,12],[8,9,19],[10,11,20],[13,14,26],[15,16,27],[17,18,30],[21,22,36],[23,24,25],[28,29,41],[31,32,39],[33,34,35],[37,38,40],[42,43,44],[45,46,49],[47,48,53],[50,51,52]]
noncomputable def verticesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (5)) (.leaf (9)))) (.branch 11 (.branch 10 (.leaf (10)) (.leaf (12))) (.branch 12 (.leaf (13)) (.leaf (8)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (15)) (.branch 15 (.leaf (16)) (.leaf (18)))) (.branch 18 (.branch 17 (.leaf (19)) (.leaf (21))) (.branch 19 (.leaf (22)) (.leaf (11))))) (.branch 23 (.branch 21 (.leaf (14)) (.branch 22 (.leaf (24)) (.leaf (25)))) (.branch 25 (.branch 24 (.leaf (27)) (.leaf (28))) (.branch 26 (.leaf (29)) (.leaf (17))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (20)) (.branch 29 (.leaf (30)) (.leaf (31)))) (.branch 31 (.leaf (23)) (.branch 32 (.leaf (33)) (.leaf (34))))) (.branch 36 (.branch 34 (.leaf (36)) (.branch 35 (.leaf (37)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (26)) (.leaf (39))) (.branch 39 (.leaf (40)) (.leaf (35)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (41)) (.branch 42 (.leaf (32)) (.leaf (42)))) (.branch 45 (.branch 44 (.leaf (43)) (.leaf (44))) (.branch 46 (.leaf (45)) (.leaf (46))))) (.branch 50 (.branch 48 (.leaf (48)) (.branch 49 (.leaf (49)) (.leaf (47)))) (.branch 52 (.branch 51 (.leaf (51)) (.leaf (52))) (.branch 53 (.leaf (53)) (.leaf (50))))))))
noncomputable def verticesIndex (p : Fin 54) : Fin 54 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (6)) (.leaf (12)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (9))) (.branch 12 (.leaf (19)) (.leaf (10)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (11)) (.branch 15 (.leaf (20)) (.leaf (13)))) (.branch 18 (.branch 17 (.leaf (14)) (.leaf (26))) (.branch 19 (.leaf (15)) (.leaf (16))))) (.branch 23 (.branch 21 (.leaf (27)) (.branch 22 (.leaf (17)) (.leaf (18)))) (.branch 25 (.branch 24 (.leaf (30)) (.leaf (21))) (.branch 26 (.leaf (22)) (.leaf (36))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (23)) (.branch 29 (.leaf (24)) (.leaf (25)))) (.branch 31 (.leaf (28)) (.branch 32 (.leaf (29)) (.leaf (41))))) (.branch 36 (.branch 34 (.leaf (31)) (.branch 35 (.leaf (32)) (.leaf (39)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (34))) (.branch 39 (.leaf (35)) (.leaf (37)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (38)) (.branch 42 (.leaf (40)) (.leaf (42)))) (.branch 45 (.branch 44 (.leaf (43)) (.leaf (44))) (.branch 46 (.leaf (45)) (.leaf (46))))) (.branch 50 (.branch 48 (.leaf (49)) (.branch 49 (.leaf (47)) (.leaf (48)))) (.branch 52 (.branch 51 (.leaf (53)) (.leaf (50))) (.branch 53 (.leaf (51)) (.leaf (52))))))))
noncomputable def verticesBack (p : Fin 54) : Fin 54 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 54, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 54 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 54, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 54)) := [[0,1],[2,3],[4,5],[6,8],[7,10],[9,13],[11,15],[12,17],[14,20],[16,21],[18,23],[19,24],[22,28],[25,31],[26,33],[27,34],[29,37],[30,39],[32,38],[35,36],[40,42],[41,43],[44,45],[46,47],[48,50],[49,51],[52,53]]
noncomputable def edgesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (10)) (.leaf (9))) (.branch 12 (.leaf (12)) (.leaf (14)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (11)) (.branch 15 (.leaf (16)) (.leaf (13)))) (.branch 18 (.branch 17 (.leaf (18)) (.leaf (15))) (.branch 19 (.leaf (20)) (.leaf (22))))) (.branch 23 (.branch 21 (.leaf (17)) (.branch 22 (.leaf (19)) (.leaf (24)))) (.branch 25 (.branch 24 (.leaf (21)) (.leaf (23))) (.branch 26 (.leaf (26)) (.leaf (28))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (30)) (.branch 29 (.leaf (25)) (.leaf (32)))) (.branch 31 (.leaf (34)) (.branch 32 (.leaf (27)) (.leaf (36))))) (.branch 36 (.branch 34 (.leaf (29)) (.branch 35 (.leaf (31)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (33))) (.branch 39 (.leaf (37)) (.leaf (35)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (40)) (.branch 42 (.leaf (42)) (.leaf (41)))) (.branch 45 (.branch 44 (.leaf (43)) (.leaf (44))) (.branch 46 (.leaf (45)) (.leaf (46))))) (.branch 50 (.branch 48 (.leaf (47)) (.branch 49 (.leaf (48)) (.leaf (50)))) (.branch 52 (.branch 51 (.leaf (49)) (.leaf (51))) (.branch 53 (.leaf (52)) (.leaf (53))))))))
noncomputable def edgesIndex (p : Fin 54) : Fin 54 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (10)) (.leaf (9))) (.branch 12 (.leaf (13)) (.leaf (11)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (15)) (.branch 15 (.leaf (12)) (.leaf (17)))) (.branch 18 (.branch 17 (.leaf (14)) (.leaf (20))) (.branch 19 (.leaf (16)) (.leaf (21))))) (.branch 23 (.branch 21 (.leaf (18)) (.branch 22 (.leaf (23)) (.leaf (19)))) (.branch 25 (.branch 24 (.leaf (24)) (.leaf (22))) (.branch 26 (.leaf (28)) (.leaf (25))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (31)) (.branch 29 (.leaf (26)) (.leaf (33)))) (.branch 31 (.leaf (27)) (.branch 32 (.leaf (34)) (.leaf (29))))) (.branch 36 (.branch 34 (.leaf (37)) (.branch 35 (.leaf (30)) (.leaf (39)))) (.branch 38 (.branch 37 (.leaf (32)) (.leaf (38))) (.branch 39 (.leaf (35)) (.leaf (36)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (40)) (.branch 42 (.leaf (42)) (.leaf (41)))) (.branch 45 (.branch 44 (.leaf (43)) (.leaf (44))) (.branch 46 (.leaf (45)) (.leaf (46))))) (.branch 50 (.branch 48 (.leaf (47)) (.branch 49 (.leaf (48)) (.leaf (50)))) (.branch 52 (.branch 51 (.leaf (49)) (.leaf (51))) (.branch 53 (.leaf (52)) (.leaf (53))))))))
noncomputable def edgesBack (p : Fin 54) : Fin 54 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 54, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 54 := by decide +kernel
theorem edges_partition : ∀ p : Fin 54, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 54)) := [[0,2,4,6,9,14,10,3],[1],[5,7,11,16,22,29,38,39,17],[8,12,18,24],[13,19,25,32,40,43,28,36,33],[15,20,26,34],[21,27,35],[23,30,31],[37,41,44,46,48,51,45,42],[47,49,52],[50,53]]
noncomputable def facesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (8)) (.leaf (1)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (2)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (10)) (.leaf (18)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (6))) (.branch 12 (.leaf (11)) (.leaf (19)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (22)) (.branch 15 (.leaf (5)) (.leaf (31)))) (.branch 18 (.branch 17 (.leaf (12)) (.leaf (17))) (.branch 19 (.leaf (20)) (.leaf (23))))) (.branch 23 (.branch 21 (.leaf (32)) (.branch 22 (.leaf (35)) (.leaf (13)))) (.branch 25 (.branch 24 (.leaf (38)) (.leaf (21))) (.branch 26 (.leaf (24)) (.leaf (33))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (36)) (.branch 29 (.leaf (28)) (.leaf (14)))) (.branch 31 (.leaf (39)) (.branch 32 (.leaf (40)) (.leaf (25))))) (.branch 36 (.branch 34 (.leaf (30)) (.branch 35 (.leaf (34)) (.leaf (37)))) (.branch 38 (.branch 37 (.leaf (29)) (.leaf (41))) (.branch 39 (.leaf (15)) (.leaf (16)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (26)) (.branch 42 (.leaf (42)) (.leaf (48)))) (.branch 45 (.branch 44 (.leaf (27)) (.leaf (43))) (.branch 46 (.leaf (47)) (.leaf (44))))) (.branch 50 (.branch 48 (.leaf (49)) (.branch 49 (.leaf (45)) (.leaf (50)))) (.branch 52 (.branch 51 (.leaf (52)) (.leaf (46))) (.branch 53 (.leaf (51)) (.leaf (53))))))))
noncomputable def facesIndex (p : Fin 54) : Fin 54 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (9)) (.leaf (14))))) (.branch 9 (.branch 7 (.leaf (10)) (.branch 8 (.leaf (3)) (.leaf (1)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (7))) (.branch 12 (.leaf (11)) (.leaf (16)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (22)) (.branch 15 (.leaf (29)) (.leaf (38)))) (.branch 18 (.branch 17 (.leaf (39)) (.leaf (17))) (.branch 19 (.leaf (8)) (.leaf (12))))) (.branch 23 (.branch 21 (.leaf (18)) (.branch 22 (.leaf (24)) (.leaf (13)))) (.branch 25 (.branch 24 (.leaf (19)) (.leaf (25))) (.branch 26 (.leaf (32)) (.leaf (40))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (43)) (.branch 29 (.leaf (28)) (.leaf (36)))) (.branch 31 (.leaf (33)) (.branch 32 (.leaf (15)) (.leaf (20))))) (.branch 36 (.branch 34 (.leaf (26)) (.branch 35 (.leaf (34)) (.leaf (21)))) (.branch 38 (.branch 37 (.leaf (27)) (.leaf (35))) (.branch 39 (.leaf (23)) (.leaf (30)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (31)) (.branch 42 (.leaf (37)) (.leaf (41)))) (.branch 45 (.branch 44 (.leaf (44)) (.leaf (46))) (.branch 46 (.leaf (48)) (.leaf (51))))) (.branch 50 (.branch 48 (.leaf (45)) (.branch 49 (.leaf (42)) (.leaf (47)))) (.branch 52 (.branch 51 (.leaf (49)) (.leaf (52))) (.branch 53 (.leaf (50)) (.leaf (53))))))))
noncomputable def facesBack (p : Fin 54) : Fin 54 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 54, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 54 := by decide +kernel
theorem faces_partition : ∀ p : Fin 54, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [8,1,9,4,9,4,3,3,8,3,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 18 - 27 + 11 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,1⟩)) (.leaf (⟨-1,-1,1,0⟩)))) (.branch 4 (.leaf (⟨-1,1,0,-1⟩)) (.branch 5 (.leaf (⟨1,2,-1,-1⟩)) (.leaf (⟨2,-1,-1,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,-3,1,2⟩)) (.branch 8 (.leaf (⟨2,1,-1,0⟩)) (.leaf (⟨-3,1,2,-1⟩)))) (.branch 11 (.branch 10 (.leaf (⟨1,4,-1,-3⟩)) (.leaf (⟨1,-2,0,1⟩))) (.branch 12 (.leaf (⟨-2,-3,1,1⟩)) (.leaf (⟨-3,-2,2,1⟩)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (⟨4,1,-1,0⟩)) (.branch 15 (.leaf (⟨-1,3,0,-1⟩)) (.leaf (⟨-3,2,1,-1⟩)))) (.branch 18 (.branch 17 (.leaf (⟨2,5,-1,-2⟩)) (.leaf (⟨-2,3,1,-2⟩))) (.branch 19 (.leaf (⟨3,5,-2,-3⟩)) (.leaf (⟨4,3,-3,-2⟩))))) (.branch 23 (.branch 21 (.leaf (⟨-3,-1,1,0⟩)) (.branch 22 (.leaf (⟨5,-2,-2,1⟩)) (.leaf (⟨-2,-7,1,3⟩)))) (.branch 25 (.branch 24 (.leaf (⟨-7,-3,5,2⟩)) (.leaf (⟨3,-4,-2,3⟩))) (.branch 26 (.leaf (⟨-4,-7,3,5⟩)) (.leaf (⟨3,4,-1,-1⟩))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (⟨5,3,-2,-1⟩)) (.branch 29 (.leaf (⟨-7,2,3,-1⟩)) (.leaf (⟨2,9,-1,-4⟩)))) (.branch 31 (.leaf (⟨5,2,-3,-1⟩)) (.branch 32 (.leaf (⟨-5,-7,3,4⟩)) (.leaf (⟨-7,-2,4,1⟩))))) (.branch 36 (.branch 34 (.leaf (⟨-8,-3,3,1⟩)) (.branch 35 (.leaf (⟨3,-5,-1,2⟩)) (.leaf (⟨-5,-8,2,3⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-7,-5,3,2⟩)) (.leaf (⟨9,2,-5,-1⟩))) (.branch 39 (.leaf (⟨-2,7,1,-4⟩)) (.leaf (⟨2,-5,-1,3⟩)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (⟨7,9,-4,-5⟩)) (.branch 42 (.leaf (⟨9,7,-4,-3⟩)) (.leaf (⟨9,-7,-5,4⟩)))) (.branch 45 (.branch 44 (.leaf (⟨-7,-16,4,9⟩)) (.leaf (⟨-16,-9,9,5⟩))) (.branch 46 (.leaf (⟨-9,16,5,-9⟩)) (.leaf (⟨16,25,-9,-14⟩))))) (.branch 50 (.branch 48 (.leaf (⟨25,-16,-14,9⟩)) (.branch 49 (.leaf (⟨-16,-41,9,23⟩)) (.leaf (⟨25,9,-14,-5⟩)))) (.branch 52 (.branch 51 (.leaf (⟨-34,-9,19,5⟩)) (.leaf (⟨9,-25,-5,14⟩))) (.branch 53 (.leaf (⟨-25,-34,14,19⟩)) (.leaf (⟨-41,-25,23,14⟩))))))))
noncomputable def liftMatrix (p : Fin 54) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 54) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],1⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],2⟩,⟨⟨-1,1,0,-1⟩,[.t (-1)],3⟩,⟨⟨1,2,-1,-1⟩,[.t (-1),.s,.t (1)],4⟩,⟨⟨2,-1,-1,1⟩,[.t (-2),.s,.t (-1)],5⟩,⟨⟨-1,-3,1,2⟩,[.t (-1),.s,.t (2)],6⟩,⟨⟨2,1,-1,0⟩,[.t (-2),.s,.t (0)],7⟩,⟨⟨-3,1,2,-1⟩,[.t (-2),.s,.t (-2),.s,.t (-1)],8⟩,⟨⟨1,4,-1,-3⟩,[.t (-1),.s,.t (3)],9⟩,⟨⟨1,-2,0,1⟩,[.t (-2)],10⟩,⟨⟨-2,-3,1,1⟩,[.t (-2),.s,.t (1)],11⟩,⟨⟨-3,-2,2,1⟩,[.t (-2),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨4,1,-1,0⟩,[.t (-4),.s,.t (0)],13⟩,⟨⟨-1,3,0,-1⟩,[.t (-3)],14⟩,⟨⟨-3,2,1,-1⟩,[.t (-3),.s,.t (-1)],15⟩,⟨⟨2,5,-1,-2⟩,[.t (-2),.s,.t (2)],16⟩,⟨⟨-2,3,1,-2⟩,[.t (-2),.s,.t (-2)],17⟩,⟨⟨3,5,-2,-3⟩,[.t (-2),.s,.t (-2),.s,.t (1)],18⟩,⟨⟨4,3,-3,-2⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],19⟩,⟨⟨-3,-1,1,0⟩,[.t (-3),.s,.t (0)],20⟩,⟨⟨5,-2,-2,1⟩,[.t (-3),.s,.t (-2),.s,.t (-1)],21⟩,⟨⟨-2,-7,1,3⟩,[.t (-2),.s,.t (3)],22⟩,⟨⟨-7,-3,5,2⟩,[.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],23⟩,⟨⟨3,-4,-2,3⟩,[.t (-2),.s,.t (-2),.s,.t (-2)],24⟩,⟨⟨-4,-7,3,5⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],25⟩,⟨⟨3,4,-1,-1⟩,[.t (-3),.s,.t (1)],26⟩,⟨⟨5,3,-2,-1⟩,[.t (-3),.s,.t (-2),.s,.t (0)],27⟩,⟨⟨-7,2,3,-1⟩,[.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-1)],28⟩,⟨⟨2,9,-1,-4⟩,[.t (-2),.s,.t (4)],29⟩,⟨⟨5,2,-3,-1⟩,[.t (-2),.s,.t (-3),.s,.t (0)],30⟩,⟨⟨-5,-7,3,4⟩,[.t (-2),.s,.t (-3),.s,.t (1)],31⟩,⟨⟨-7,-2,4,1⟩,[.t (-2),.s,.t (-4),.s,.t (0)],32⟩,⟨⟨-8,-3,3,1⟩,[.t (-3),.s,.t (-3),.s,.t (0)],33⟩,⟨⟨3,-5,-1,2⟩,[.t (-3),.s,.t (-2)],34⟩,⟨⟨-5,-8,2,3⟩,[.t (-3),.s,.t (-2),.s,.t (1)],35⟩,⟨⟨-7,-5,3,2⟩,[.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],36⟩,⟨⟨9,2,-5,-1⟩,[.t (-2),.s,.t (-5),.s,.t (0)],37⟩,⟨⟨-2,7,1,-4⟩,[.t (-2),.s,.t (-4)],38⟩,⟨⟨2,-5,-1,3⟩,[.t (-2),.s,.t (-3)],39⟩,⟨⟨7,9,-4,-5⟩,[.t (-2),.s,.t (-4),.s,.t (1)],40⟩,⟨⟨9,7,-4,-3⟩,[.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],41⟩,⟨⟨9,-7,-5,4⟩,[.t (-2),.s,.t (-5),.s,.t (-1)],42⟩,⟨⟨-7,-16,4,9⟩,[.t (-2),.s,.t (-4),.s,.t (2)],43⟩,⟨⟨-16,-9,9,5⟩,[.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (0)],44⟩,⟨⟨-9,16,5,-9⟩,[.t (-2),.s,.t (-5),.s,.t (-2)],45⟩,⟨⟨16,25,-9,-14⟩,[.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (1)],46⟩,⟨⟨25,-16,-14,9⟩,[.t (-2),.s,.t (-5),.s,.t (-3),.s,.t (-1)],47⟩,⟨⟨-16,-41,9,23⟩,[.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (2)],48⟩,⟨⟨25,9,-14,-5⟩,[.t (-2),.s,.t (-5),.s,.t (-3),.s,.t (0)],49⟩,⟨⟨-34,-9,19,5⟩,[.t (-2),.s,.t (-5),.s,.t (-4),.s,.t (0)],50⟩,⟨⟨9,-25,-5,14⟩,[.t (-2),.s,.t (-5),.s,.t (-3)],51⟩,⟨⟨-25,-34,14,19⟩,[.t (-2),.s,.t (-5),.s,.t (-3),.s,.t (1)],52⟩,⟨⟨-41,-25,23,14⟩,[.t (-2),.s,.t (-5),.s,.t (-3),.s,.t (-2),.s,.t (0)],53⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 54 ∧ ((List.finRange 54).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 54) := [⟨13,2,⟨⟨1,8,-1,-7⟩,[.t (-1),.s,.t (7)],0⟩⟩,⟨26,5,⟨⟨11,36,-4,-13⟩,[.t (-3),.s,.t (-4),.s,.t (3)],0⟩⟩,⟨33,5,⟨⟨-13,-36,4,11⟩,[.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (2)],0⟩⟩,⟨35,7,⟨⟨-29,-75,12,31⟩,[.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (2)],0⟩⟩,⟨36,7,⟨⟨31,75,-12,-29⟩,[.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (2)],0⟩⟩,⟨41,8,⟨⟨76,175,-43,-99⟩,[.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (2)],0⟩⟩,⟨29,6,⟨⟨-17,-36,9,19⟩,[.t (-2),.s,.t (-9),.s,.t (2)],0⟩⟩,⟨37,6,⟨⟨19,36,-9,-17⟩,[.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨50,9,⟨⟨509,913,-286,-513⟩,[.t (-2),.s,.t (-5),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨52,10,⟨⟨-1049,-1875,588,1051⟩,[.t (-2),.s,.t (-5),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨53,10,⟨⟨1051,1875,-588,-1049⟩,[.t (-2),.s,.t (-5),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨48,9,⟨⟨-513,-913,286,509⟩,[.t (-2),.s,.t (-5),.s,.t (-7),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨43,8,⟨⟨-99,-175,43,76⟩,[.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨31,4,⟨⟨40,69,-29,-50⟩,[.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨18,3,⟨⟨23,36,-16,-25⟩,[.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨23,3,⟨⟨-25,-36,16,23⟩,[.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (1)],0⟩⟩,⟨25,4,⟨⟨-50,-69,29,40⟩,[.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-3),.s,.t (1)],0⟩⟩,⟨9,2,⟨⟨-7,-8,1,1⟩,[.t (-7),.s,.t (1)],0⟩⟩,⟨1,1,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],0⟩⟩,⟨0,1,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-4,1),(-3,1),(-8,3),(-5,2),(-7,3),(-9,4),(-2,1),(-9,5),(-34,19),(-25,14),(-41,23),(-16,9),(-7,4),(-5,3),(-3,2),(-7,5),(-4,3),(-1,1),(0,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end PSL2_17_c1

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
