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
namespace PSL2_17_c4
noncomputable def originalSData : LookupTree (Fin 108) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (9)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (0)) (.leaf (13)))) (.branch 11 (.branch 10 (.leaf (12)) (.leaf (16))) (.branch 12 (.leaf (14)) (.leaf (19)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (2)) (.branch 15 (.leaf (21)) (.leaf (22)))) (.branch 18 (.branch 17 (.leaf (20)) (.leaf (25))) (.branch 19 (.leaf (26)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (28)) (.branch 22 (.leaf (6)) (.leaf (27)))) (.branch 25 (.branch 24 (.leaf (31)) (.leaf (33))) (.branch 26 (.leaf (29)) (.leaf (30))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (36)) (.branch 29 (.leaf (10)) (.leaf (39)))) (.branch 31 (.leaf (40)) (.branch 32 (.leaf (37)) (.leaf (41))))) (.branch 36 (.branch 34 (.leaf (38)) (.branch 35 (.leaf (43)) (.leaf (45)))) (.branch 38 (.branch 37 (.leaf (15)) (.leaf (47))) (.branch 39 (.leaf (49)) (.leaf (17)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (18)) (.branch 42 (.leaf (48)) (.leaf (53)))) (.branch 45 (.branch 44 (.leaf (50)) (.leaf (52))) (.branch 46 (.leaf (51)) (.leaf (56))))) (.branch 50 (.branch 48 (.leaf (23)) (.branch 49 (.leaf (57)) (.leaf (24)))) (.branch 52 (.branch 51 (.leaf (59)) (.leaf (61))) (.branch 53 (.leaf (60)) (.leaf (58)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (65)) (.branch 56 (.leaf (67)) (.leaf (62)))) (.branch 58 (.leaf (32)) (.branch 59 (.leaf (71)) (.leaf (34))))) (.branch 63 (.branch 61 (.leaf (70)) (.branch 62 (.leaf (35)) (.leaf (69)))) (.branch 65 (.branch 64 (.leaf (74)) (.leaf (75))) (.branch 66 (.leaf (72)) (.leaf (78)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (73)) (.branch 69 (.leaf (79)) (.leaf (46)))) (.branch 72 (.branch 71 (.leaf (44)) (.leaf (42))) (.branch 73 (.leaf (82)) (.leaf (84))))) (.branch 77 (.branch 75 (.leaf (80)) (.branch 76 (.leaf (81)) (.leaf (86)))) (.branch 79 (.branch 78 (.leaf (87)) (.leaf (83))) (.branch 80 (.leaf (85)) (.leaf (91))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (92)) (.branch 83 (.leaf (54)) (.leaf (90)))) (.branch 85 (.leaf (55)) (.branch 86 (.leaf (95)) (.leaf (93))))) (.branch 90 (.branch 88 (.leaf (94)) (.branch 89 (.leaf (96)) (.leaf (97)))) (.branch 92 (.branch 91 (.leaf (66)) (.leaf (63))) (.branch 93 (.leaf (64)) (.leaf (100)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (101)) (.branch 96 (.leaf (68)) (.leaf (102)))) (.branch 99 (.branch 98 (.leaf (99)) (.leaf (104))) (.branch 100 (.leaf (105)) (.leaf (76))))) (.branch 104 (.branch 102 (.leaf (77)) (.branch 103 (.leaf (107)) (.leaf (98)))) (.branch 106 (.branch 105 (.leaf (106)) (.leaf (89))) (.branch 107 (.leaf (103)) (.leaf (88)))))))))
noncomputable def originalS (p : Fin 108) : Fin 108 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 108) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (10)) (.leaf (11))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (12)) (.leaf (14)))) (.branch 11 (.branch 10 (.leaf (15)) (.leaf (17))) (.branch 12 (.leaf (18)) (.leaf (20)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (21)) (.branch 15 (.leaf (1)) (.leaf (23)))) (.branch 18 (.branch 17 (.leaf (24)) (.leaf (22))) (.branch 19 (.leaf (26)) (.leaf (27))))) (.branch 23 (.branch 21 (.leaf (29)) (.branch 22 (.leaf (30)) (.leaf (3)))) (.branch 25 (.branch 24 (.leaf (32)) (.leaf (34))) (.branch 26 (.leaf (35)) (.leaf (5))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (37)) (.branch 29 (.leaf (38)) (.leaf (36)))) (.branch 31 (.leaf (40)) (.branch 32 (.leaf (39)) (.leaf (42))))) (.branch 36 (.branch 34 (.leaf (9)) (.branch 35 (.leaf (44)) (.leaf (46)))) (.branch 38 (.branch 37 (.leaf (0)) (.leaf (48))) (.branch 39 (.leaf (50)) (.leaf (51)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (13)) (.branch 42 (.leaf (52)) (.leaf (54)))) (.branch 45 (.branch 44 (.leaf (55)) (.leaf (47))) (.branch 46 (.leaf (16)) (.leaf (45))))) (.branch 50 (.branch 48 (.leaf (25)) (.branch 49 (.leaf (58)) (.leaf (19)))) (.branch 52 (.branch 51 (.leaf (60)) (.leaf (62))) (.branch 53 (.leaf (63)) (.leaf (64)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (66)) (.branch 56 (.leaf (68)) (.leaf (69)))) (.branch 58 (.leaf (70)) (.branch 59 (.leaf (72)) (.leaf (73))))) (.branch 63 (.branch 61 (.leaf (31)) (.branch 62 (.leaf (28)) (.leaf (61)))) (.branch 65 (.branch 64 (.leaf (74)) (.leaf (76))) (.branch 66 (.leaf (77)) (.leaf (67)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (33)) (.branch 69 (.leaf (75)) (.leaf (56)))) (.branch 72 (.branch 71 (.leaf (80)) (.leaf (81))) (.branch 73 (.leaf (83)) (.leaf (85))))) (.branch 77 (.branch 75 (.leaf (43)) (.branch 76 (.leaf (41)) (.leaf (86)))) (.branch 79 (.branch 78 (.leaf (88)) (.leaf (89))) (.branch 80 (.leaf (90)) (.leaf (91))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (93)) (.branch 83 (.leaf (94)) (.leaf (84)))) (.branch 85 (.leaf (49)) (.branch 86 (.leaf (92)) (.leaf (95))))) (.branch 90 (.branch 88 (.leaf (53)) (.branch 89 (.leaf (97)) (.leaf (98)))) (.branch 92 (.branch 91 (.leaf (99)) (.leaf (59))) (.branch 93 (.leaf (57)) (.leaf (100)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (102)) (.branch 96 (.leaf (78)) (.leaf (103)))) (.branch 99 (.branch 98 (.leaf (65)) (.leaf (87))) (.branch 100 (.leaf (106)) (.leaf (79))))) (.branch 104 (.branch 102 (.leaf (71)) (.branch 103 (.leaf (105)) (.leaf (96)))) (.branch 106 (.branch 105 (.leaf (107)) (.leaf (82))) (.branch 107 (.leaf (101)) (.leaf (104)))))))))
noncomputable def originalT (p : Fin 108) : Fin 108 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 54) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (8)) (.leaf (3)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (4)) (.branch 15 (.leaf (5)) (.leaf (9)))) (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (12)) (.leaf (6))))) (.branch 23 (.branch 21 (.leaf (7)) (.branch 22 (.leaf (8)) (.leaf (13)))) (.branch 25 (.branch 24 (.leaf (14)) (.leaf (15))) (.branch 26 (.leaf (16)) (.leaf (17))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (11)))) (.branch 31 (.leaf (12)) (.branch 32 (.leaf (18)) (.leaf (19))))) (.branch 36 (.branch 34 (.leaf (20)) (.branch 35 (.leaf (21)) (.leaf (22)))) (.branch 38 (.branch 37 (.leaf (13)) (.leaf (14))) (.branch 39 (.leaf (15)) (.leaf (16)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (17)) (.branch 42 (.leaf (23)) (.leaf (24)))) (.branch 45 (.branch 44 (.leaf (25)) (.leaf (26))) (.branch 46 (.leaf (27)) (.leaf (28))))) (.branch 50 (.branch 48 (.leaf (18)) (.branch 49 (.leaf (19)) (.leaf (20)))) (.branch 52 (.branch 51 (.leaf (21)) (.leaf (22))) (.branch 53 (.leaf (29)) (.leaf (30)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (31)) (.branch 56 (.leaf (32)) (.leaf (33)))) (.branch 58 (.leaf (23)) (.branch 59 (.leaf (24)) (.leaf (25))))) (.branch 63 (.branch 61 (.leaf (26)) (.branch 62 (.leaf (27)) (.leaf (28)))) (.branch 65 (.branch 64 (.leaf (34)) (.leaf (35))) (.branch 66 (.leaf (36)) (.leaf (37)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (38)) (.branch 69 (.leaf (39)) (.leaf (33)))) (.branch 72 (.branch 71 (.leaf (29)) (.leaf (30))) (.branch 73 (.leaf (31)) (.leaf (32))))) (.branch 77 (.branch 75 (.leaf (40)) (.branch 76 (.leaf (41)) (.leaf (42)))) (.branch 79 (.branch 78 (.leaf (43)) (.leaf (44))) (.branch 80 (.leaf (45)) (.leaf (34))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (35)) (.branch 83 (.leaf (36)) (.leaf (37)))) (.branch 85 (.leaf (38)) (.branch 86 (.leaf (39)) (.leaf (46))))) (.branch 90 (.branch 88 (.leaf (47)) (.branch 89 (.leaf (48)) (.leaf (49)))) (.branch 92 (.branch 91 (.leaf (44)) (.leaf (40))) (.branch 93 (.leaf (41)) (.leaf (42)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (43)) (.branch 96 (.leaf (45)) (.leaf (50)))) (.branch 99 (.branch 98 (.leaf (51)) (.leaf (52))) (.branch 100 (.leaf (49)) (.leaf (46))))) (.branch 104 (.branch 102 (.leaf (47)) (.branch 103 (.leaf (48)) (.leaf (53)))) (.branch 106 (.branch 105 (.leaf (53)) (.leaf (51))) (.branch 107 (.leaf (52)) (.leaf (50)))))))))
noncomputable def projection (p : Fin 108) : Fin 54 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 108) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (11)))) (.branch 11 (.branch 10 (.leaf (15)) (.leaf (16))) (.branch 12 (.leaf (17)) (.leaf (18)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (22)) (.branch 15 (.leaf (23)) (.leaf (24)))) (.branch 18 (.branch 17 (.leaf (25)) (.leaf (26))) (.branch 19 (.leaf (31)) (.leaf (32))))) (.branch 23 (.branch 21 (.leaf (33)) (.branch 22 (.leaf (34)) (.leaf (35)))) (.branch 25 (.branch 24 (.leaf (41)) (.leaf (42))) (.branch 26 (.leaf (43)) (.leaf (44))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (45)) (.branch 29 (.leaf (46)) (.leaf (52)))) (.branch 31 (.leaf (53)) (.branch 32 (.leaf (54)) (.leaf (55))))) (.branch 36 (.branch 34 (.leaf (56)) (.branch 35 (.leaf (63)) (.leaf (64)))) (.branch 38 (.branch 37 (.leaf (65)) (.leaf (66))) (.branch 39 (.leaf (67)) (.leaf (68)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (74)) (.branch 42 (.leaf (75)) (.leaf (76)))) (.branch 45 (.branch 44 (.leaf (77)) (.leaf (78))) (.branch 46 (.leaf (79)) (.leaf (86))))) (.branch 50 (.branch 48 (.leaf (87)) (.branch 49 (.leaf (88)) (.leaf (89)))) (.branch 52 (.branch 51 (.leaf (96)) (.leaf (97))) (.branch 53 (.leaf (98)) (.leaf (103))))))))
noncomputable def representative (p : Fin 54) : Fin 108 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (10)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (13)) (.leaf (7))) (.branch 12 (.leaf (16)) (.leaf (17)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (9)) (.branch 15 (.leaf (18)) (.leaf (20)))) (.branch 18 (.branch 17 (.leaf (11)) (.leaf (12))) (.branch 19 (.leaf (14)) (.leaf (23))))) (.branch 23 (.branch 21 (.leaf (15)) (.branch 22 (.leaf (25)) (.leaf (27)))) (.branch 25 (.branch 24 (.leaf (19)) (.leaf (30))) (.branch 26 (.leaf (21)) (.leaf (29))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (22)) (.branch 29 (.leaf (33)) (.leaf (26)))) (.branch 31 (.leaf (24)) (.branch 32 (.leaf (36)) (.leaf (38))))) (.branch 36 (.branch 34 (.leaf (28)) (.branch 35 (.leaf (40)) (.leaf (41)))) (.branch 38 (.branch 37 (.leaf (31)) (.leaf (44))) (.branch 39 (.leaf (32)) (.leaf (45)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (34)) (.branch 42 (.leaf (35)) (.leaf (46)))) (.branch 45 (.branch 44 (.leaf (47)) (.leaf (37))) (.branch 46 (.leaf (39)) (.leaf (42))))) (.branch 50 (.branch 48 (.leaf (43)) (.branch 49 (.leaf (50)) (.leaf (51)))) (.branch 52 (.branch 51 (.leaf (48)) (.leaf (49))) (.branch 53 (.leaf (53)) (.leaf (52))))))))
noncomputable def S (p : Fin 54) : Fin 54 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (8)) (.leaf (1))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (12)))) (.branch 11 (.branch 10 (.leaf (14)) (.leaf (15))) (.branch 12 (.leaf (13)) (.leaf (17)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (19)) (.leaf (21)))) (.branch 18 (.branch 17 (.leaf (22)) (.leaf (4))) (.branch 19 (.leaf (16)) (.leaf (24))))) (.branch 23 (.branch 21 (.leaf (6)) (.branch 22 (.leaf (26)) (.leaf (28)))) (.branch 25 (.branch 24 (.leaf (29)) (.leaf (31))) (.branch 26 (.leaf (32)) (.leaf (18))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (10)) (.branch 29 (.leaf (27)) (.leaf (34)))) (.branch 31 (.leaf (35)) (.branch 32 (.leaf (37)) (.leaf (39))))) (.branch 36 (.branch 34 (.leaf (33)) (.branch 35 (.leaf (40)) (.leaf (42)))) (.branch 38 (.branch 37 (.leaf (43)) (.leaf (38))) (.branch 39 (.leaf (20)) (.leaf (41)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (25)) (.branch 42 (.leaf (23)) (.leaf (46)))) (.branch 45 (.branch 44 (.leaf (48)) (.leaf (49))) (.branch 46 (.leaf (44)) (.leaf (45))))) (.branch 50 (.branch 48 (.leaf (30)) (.branch 49 (.leaf (51)) (.leaf (52)))) (.branch 52 (.branch 51 (.leaf (53)) (.leaf (36))) (.branch 53 (.leaf (47)) (.leaf (50))))))))
noncomputable def T (p : Fin 54) : Fin 54 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (13)) (.branch 2 (.leaf (5)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (17)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (20)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (27))) (.branch 12 (.leaf (7)) (.leaf (8)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (11)) (.branch 15 (.leaf (9)) (.leaf (10)))) (.branch 18 (.branch 17 (.leaf (18)) (.leaf (12))) (.branch 19 (.leaf (26)) (.leaf (14))))) (.branch 23 (.branch 21 (.leaf (38)) (.branch 22 (.leaf (15)) (.leaf (16)))) (.branch 25 (.branch 24 (.leaf (41)) (.leaf (19))) (.branch 26 (.leaf (40)) (.leaf (21))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (28)) (.branch 29 (.leaf (22)) (.leaf (23)))) (.branch 31 (.leaf (47)) (.branch 32 (.leaf (24)) (.leaf (25))))) (.branch 36 (.branch 34 (.leaf (33)) (.branch 35 (.leaf (29)) (.leaf (30)))) (.branch 38 (.branch 37 (.leaf (51)) (.leaf (31))) (.branch 39 (.leaf (37)) (.leaf (32)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (34)) (.branch 42 (.leaf (39)) (.leaf (35)))) (.branch 45 (.branch 44 (.leaf (36)) (.leaf (45))) (.branch 46 (.leaf (46)) (.leaf (42))))) (.branch 50 (.branch 48 (.leaf (52)) (.branch 49 (.leaf (43)) (.leaf (44)))) (.branch 52 (.branch 51 (.leaf (53)) (.leaf (48))) (.branch 53 (.leaf (49)) (.leaf (50))))))))
noncomputable def Ti (p : Fin 54) : Fin 54 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 54) : Fin 54 := T (S p)
theorem quotient_relations : (∀ p : Fin 54, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 108, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 108, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 54, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 54)) := [[0,3,9],[1,2,8],[4,5,12],[6,7,15],[10,11,22],[13,14,16],[17],[18,19,29],[20,21,32],[23,24,35],[25,26,34],[27,28,33],[30,31,43],[36,37,49],[38,39,44],[40],[41,42,45],[46],[47,48,53],[50,51,52]]
noncomputable def verticesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (2)) (.leaf (12))) (.branch 12 (.leaf (13)) (.leaf (8)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (15)) (.branch 15 (.leaf (16)) (.leaf (11)))) (.branch 18 (.branch 17 (.leaf (17)) (.leaf (18))) (.branch 19 (.leaf (19)) (.leaf (20))))) (.branch 23 (.branch 21 (.leaf (22)) (.branch 22 (.leaf (23)) (.leaf (14)))) (.branch 25 (.branch 24 (.leaf (25)) (.leaf (26))) (.branch 26 (.leaf (28)) (.leaf (29))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (31)) (.branch 29 (.leaf (32)) (.leaf (21)))) (.branch 31 (.leaf (34)) (.branch 32 (.leaf (35)) (.leaf (24))))) (.branch 36 (.branch 34 (.leaf (33)) (.branch 35 (.leaf (30)) (.leaf (27)))) (.branch 38 (.branch 37 (.leaf (37)) (.leaf (38))) (.branch 39 (.leaf (40)) (.leaf (41)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (43)) (.branch 42 (.leaf (44)) (.leaf (45)))) (.branch 45 (.branch 44 (.leaf (36)) (.leaf (42))) (.branch 46 (.leaf (46)) (.leaf (47))))) (.branch 50 (.branch 48 (.leaf (48)) (.branch 49 (.leaf (49)) (.leaf (39)))) (.branch 52 (.branch 51 (.leaf (51)) (.leaf (52))) (.branch 53 (.leaf (53)) (.leaf (50))))))))
noncomputable def verticesIndex (p : Fin 54) : Fin 54 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (9)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (12)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (15)) (.leaf (10)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (11)) (.branch 15 (.leaf (22)) (.leaf (13)))) (.branch 18 (.branch 17 (.leaf (14)) (.leaf (16))) (.branch 19 (.leaf (17)) (.leaf (18))))) (.branch 23 (.branch 21 (.leaf (19)) (.branch 22 (.leaf (29)) (.leaf (20)))) (.branch 25 (.branch 24 (.leaf (21)) (.leaf (32))) (.branch 26 (.leaf (23)) (.leaf (24))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (35)) (.branch 29 (.leaf (25)) (.leaf (26)))) (.branch 31 (.leaf (34)) (.branch 32 (.leaf (27)) (.leaf (28))))) (.branch 36 (.branch 34 (.leaf (33)) (.branch 35 (.leaf (30)) (.leaf (31)))) (.branch 38 (.branch 37 (.leaf (43)) (.leaf (36))) (.branch 39 (.leaf (37)) (.leaf (49)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (38)) (.branch 42 (.leaf (39)) (.leaf (44)))) (.branch 45 (.branch 44 (.leaf (40)) (.leaf (41))) (.branch 46 (.leaf (42)) (.leaf (45))))) (.branch 50 (.branch 48 (.leaf (46)) (.branch 49 (.leaf (47)) (.leaf (48)))) (.branch 52 (.branch 51 (.leaf (53)) (.leaf (50))) (.branch 53 (.leaf (51)) (.leaf (52))))))))
noncomputable def verticesBack (p : Fin 54) : Fin 54 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 54, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 54 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 54, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 54)) := [[0,1],[2,4],[3,6],[5,8],[7,10],[9,13],[11,16],[12,17],[14,18],[15,20],[19,23],[21,25],[22,27],[24,30],[26,29],[28,33],[31,36],[32,38],[34,40],[35,41],[37,44],[39,45],[42,46],[43,47],[48,50],[49,51],[52,53]]
noncomputable def edgesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (10)) (.leaf (9))) (.branch 12 (.leaf (12)) (.leaf (14)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (11)) (.branch 15 (.leaf (16)) (.leaf (18)))) (.branch 18 (.branch 17 (.leaf (13)) (.leaf (15))) (.branch 19 (.leaf (17)) (.leaf (20))))) (.branch 23 (.branch 21 (.leaf (19)) (.branch 22 (.leaf (22)) (.leaf (24)))) (.branch 25 (.branch 24 (.leaf (21)) (.leaf (26))) (.branch 26 (.leaf (23)) (.leaf (28))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (25)) (.branch 29 (.leaf (30)) (.leaf (29)))) (.branch 31 (.leaf (27)) (.branch 32 (.leaf (32)) (.leaf (34))))) (.branch 36 (.branch 34 (.leaf (31)) (.branch 35 (.leaf (36)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (40))) (.branch 39 (.leaf (35)) (.leaf (42)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (37)) (.branch 42 (.leaf (39)) (.leaf (44)))) (.branch 45 (.branch 44 (.leaf (46)) (.leaf (41))) (.branch 46 (.leaf (43)) (.leaf (45))))) (.branch 50 (.branch 48 (.leaf (47)) (.branch 49 (.leaf (48)) (.leaf (50)))) (.branch 52 (.branch 51 (.leaf (49)) (.leaf (51))) (.branch 53 (.leaf (52)) (.leaf (53))))))))
noncomputable def edgesIndex (p : Fin 54) : Fin 54 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (10)) (.leaf (9))) (.branch 12 (.leaf (13)) (.leaf (11)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (16)) (.branch 15 (.leaf (12)) (.leaf (17)))) (.branch 18 (.branch 17 (.leaf (14)) (.leaf (18))) (.branch 19 (.leaf (15)) (.leaf (20))))) (.branch 23 (.branch 21 (.leaf (19)) (.branch 22 (.leaf (23)) (.leaf (21)))) (.branch 25 (.branch 24 (.leaf (25)) (.leaf (22))) (.branch 26 (.leaf (27)) (.leaf (24))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (30)) (.branch 29 (.leaf (26)) (.leaf (29)))) (.branch 31 (.leaf (28)) (.branch 32 (.leaf (33)) (.leaf (31))))) (.branch 36 (.branch 34 (.leaf (36)) (.branch 35 (.leaf (32)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (34)) (.leaf (40))) (.branch 39 (.leaf (35)) (.leaf (41)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (37)) (.branch 42 (.leaf (44)) (.leaf (39)))) (.branch 45 (.branch 44 (.leaf (45)) (.leaf (42))) (.branch 46 (.leaf (46)) (.leaf (43))))) (.branch 50 (.branch 48 (.leaf (47)) (.branch 49 (.leaf (48)) (.leaf (50)))) (.branch 52 (.branch 51 (.leaf (49)) (.leaf (51))) (.branch 53 (.leaf (52)) (.leaf (53))))))))
noncomputable def edgesBack (p : Fin 54) : Fin 54 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 54, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 54 := by decide +kernel
theorem edges_partition : ∀ p : Fin 54, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 54)) := [[0,2,5,1,3,7,11,13],[4,8,12,17],[6,9,14,19,24,31,37,38,20],[10,15,21,26,18,16,22,28,27],[23,29,34,40,25,32,39,41],[30,35,42,46,45,44,49,52,47],[33],[36,43,48,51],[50,53]]
noncomputable def facesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (8)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (12)) (.branch 8 (.leaf (5)) (.leaf (9)))) (.branch 11 (.branch 10 (.leaf (13)) (.leaf (21))) (.branch 12 (.leaf (6)) (.leaf (10)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (14)) (.leaf (22)))) (.branch 18 (.branch 17 (.leaf (26)) (.leaf (11))) (.branch 19 (.leaf (25)) (.leaf (15))))) (.branch 23 (.branch 21 (.leaf (20)) (.branch 22 (.leaf (23)) (.leaf (27)))) (.branch 25 (.branch 24 (.leaf (30)) (.leaf (16))) (.branch 26 (.leaf (34)) (.leaf (24))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (29)) (.branch 29 (.leaf (28)) (.leaf (31)))) (.branch 31 (.leaf (38)) (.branch 32 (.leaf (17)) (.leaf (35))))) (.branch 36 (.branch 34 (.leaf (47)) (.branch 35 (.leaf (32)) (.leaf (39)))) (.branch 38 (.branch 37 (.leaf (48)) (.leaf (18))) (.branch 39 (.leaf (19)) (.leaf (36)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (33)) (.branch 42 (.leaf (37)) (.leaf (40)))) (.branch 45 (.branch 44 (.leaf (49)) (.leaf (43))) (.branch 46 (.leaf (42)) (.leaf (41))))) (.branch 50 (.branch 48 (.leaf (46)) (.branch 49 (.leaf (50)) (.leaf (44)))) (.branch 52 (.branch 51 (.leaf (52)) (.leaf (51))) (.branch 53 (.leaf (45)) (.leaf (53))))))))
noncomputable def facesIndex (p : Fin 54) : Fin 54 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (12))) (.branch 12 (.leaf (17)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (9)) (.branch 15 (.leaf (14)) (.leaf (19)))) (.branch 18 (.branch 17 (.leaf (24)) (.leaf (31))) (.branch 19 (.leaf (37)) (.leaf (38))))) (.branch 23 (.branch 21 (.leaf (20)) (.branch 22 (.leaf (10)) (.leaf (15)))) (.branch 25 (.branch 24 (.leaf (21)) (.leaf (26))) (.branch 26 (.leaf (18)) (.leaf (16))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (22)) (.branch 29 (.leaf (28)) (.leaf (27)))) (.branch 31 (.leaf (23)) (.branch 32 (.leaf (29)) (.leaf (34))))) (.branch 36 (.branch 34 (.leaf (40)) (.branch 35 (.leaf (25)) (.leaf (32)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (41))) (.branch 39 (.leaf (30)) (.leaf (35)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (42)) (.branch 42 (.leaf (46)) (.leaf (45)))) (.branch 45 (.branch 44 (.leaf (44)) (.leaf (49))) (.branch 46 (.leaf (52)) (.leaf (47))))) (.branch 50 (.branch 48 (.leaf (33)) (.branch 49 (.leaf (36)) (.leaf (43)))) (.branch 52 (.branch 51 (.leaf (48)) (.leaf (51))) (.branch 53 (.leaf (50)) (.leaf (53))))))))
noncomputable def facesBack (p : Fin 54) : Fin 54 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 54, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 54 := by decide +kernel
theorem faces_partition : ∀ p : Fin 54, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [8,4,9,9,8,9,1,4,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 20 - 27 + 9 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 3 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))) (.branch 11 (.branch 10 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,0,-2,1⟩))) (.branch 12 (.leaf (⟨0,-1,1,3⟩)) (.leaf (⟨2,1,1,1⟩)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (⟨-1,1,0,-1⟩)) (.branch 15 (.leaf (⟨1,2,-1,-1⟩)) (.leaf (⟨1,1,-2,-1⟩)))) (.branch 18 (.branch 17 (.leaf (⟨2,1,-1,0⟩)) (.leaf (⟨1,-2,1,-1⟩))) (.branch 19 (.leaf (⟨2,-1,-1,1⟩)) (.leaf (⟨-1,-3,1,2⟩))))) (.branch 23 (.branch 21 (.leaf (⟨1,-1,-1,2⟩)) (.branch 22 (.leaf (⟨-1,-2,2,3⟩)) (.leaf (⟨-1,-1,3,2⟩)))) (.branch 25 (.branch 24 (.leaf (⟨-3,1,2,-1⟩)) (.leaf (⟨1,4,-1,-3⟩))) (.branch 26 (.leaf (⟨-2,1,3,-2⟩)) (.leaf (⟨1,3,-2,-5⟩))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (⟨-1,1,2,-3⟩)) (.branch 29 (.leaf (⟨1,2,-3,-5⟩)) (.leaf (⟨-3,-2,2,1⟩)))) (.branch 31 (.leaf (⟨4,-1,-3,1⟩)) (.branch 32 (.leaf (⟨-1,-5,1,4⟩)) (.leaf (⟨-2,-1,3,1⟩))))) (.branch 36 (.branch 34 (.leaf (⟨2,1,-5,-2⟩)) (.branch 35 (.leaf (⟨3,2,-5,-3⟩)) (.leaf (⟨4,3,-3,-2⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-4,-1,5,1⟩)) (.leaf (⟨1,-3,-1,4⟩))) (.branch 39 (.leaf (⟨-1,2,1,-3⟩)) (.leaf (⟨2,3,-3,-4⟩)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (⟨2,-3,-3,5⟩)) (.branch 42 (.leaf (⟨-2,-5,3,7⟩)) (.leaf (⟨-5,-3,7,4⟩)))) (.branch 45 (.branch 44 (.leaf (⟨-5,-4,4,3⟩)) (.leaf (⟨3,1,-4,-1⟩))) (.branch 46 (.leaf (⟨3,-2,-4,3⟩)) (.leaf (⟨-3,5,4,-7⟩))))) (.branch 50 (.branch 48 (.leaf (⟨-4,5,3,-4⟩)) (.branch 49 (.leaf (⟨5,9,-4,-7⟩)) (.leaf (⟨-3,-4,4,5⟩)))) (.branch 52 (.branch 51 (.leaf (⟨7,4,-9,-5⟩)) (.leaf (⟨-4,3,5,-4⟩))) (.branch 53 (.leaf (⟨3,7,-4,-9⟩)) (.leaf (⟨9,4,-7,-3⟩))))))))
noncomputable def liftMatrix (p : Fin 54) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 54) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],10⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],11⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],12⟩,⟨⟨-1,1,0,-1⟩,[.t (-1)],13⟩,⟨⟨1,2,-1,-1⟩,[.t (-1),.s,.t (1)],14⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],15⟩,⟨⟨2,1,-1,0⟩,[.t (-2),.s,.t (0)],16⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],17⟩,⟨⟨2,-1,-1,1⟩,[.t (-2),.s,.t (-1)],18⟩,⟨⟨-1,-3,1,2⟩,[.t (-1),.s,.t (2)],19⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],20⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],21⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],22⟩,⟨⟨-3,1,2,-1⟩,[.t (-2),.s,.t (-2),.s,.t (-1)],23⟩,⟨⟨1,4,-1,-3⟩,[.t (-1),.s,.t (3)],24⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],25⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],26⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],27⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],28⟩,⟨⟨-3,-2,2,1⟩,[.t (-2),.s,.t (-2),.s,.t (0)],29⟩,⟨⟨4,-1,-3,1⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],30⟩,⟨⟨-1,-5,1,4⟩,[.t (-1),.s,.t (4)],31⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],32⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],33⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],34⟩,⟨⟨4,3,-3,-2⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],35⟩,⟨⟨-4,-1,5,1⟩,[.t (-1),.s,.t (-5),.s,.t (0)],36⟩,⟨⟨1,-3,-1,4⟩,[.t (-1),.s,.t (-4)],37⟩,⟨⟨-1,2,1,-3⟩,[.t (-1),.s,.t (-3)],38⟩,⟨⟨2,3,-3,-4⟩,[.t (-1),.s,.t (-3),.s,.t (1)],39⟩,⟨⟨2,-3,-3,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2)],40⟩,⟨⟨-2,-5,3,7⟩,[.t (-1),.s,.t (-3),.s,.t (2)],41⟩,⟨⟨-5,-3,7,4⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (0)],42⟩,⟨⟨-5,-4,4,3⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],43⟩,⟨⟨3,1,-4,-1⟩,[.t (-1),.s,.t (-4),.s,.t (0)],44⟩,⟨⟨3,-2,-4,3⟩,[.t (-1),.s,.t (-4),.s,.t (-1)],45⟩,⟨⟨-3,5,4,-7⟩,[.t (-1),.s,.t (-4),.s,.t (-2)],46⟩,⟨⟨-4,5,3,-4⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],47⟩,⟨⟨5,9,-4,-7⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],48⟩,⟨⟨-3,-4,4,5⟩,[.t (-1),.s,.t (-4),.s,.t (1)],49⟩,⟨⟨7,4,-9,-5⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (0)],50⟩,⟨⟨-4,3,5,-4⟩,[.t (-1),.s,.t (-5),.s,.t (-1)],51⟩,⟨⟨3,7,-4,-9⟩,[.t (-1),.s,.t (-4),.s,.t (2)],52⟩,⟨⟨9,4,-7,-3⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],53⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 54 ∧ ((List.finRange 54).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 54) := [⟨16,2,⟨⟨0,-1,1,5⟩,[.t (0),.s,.t (5)],0⟩⟩,⟨29,3,⟨⟨-5,-9,9,16⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],0⟩⟩,⟨35,6,⟨⟨16,23,-23,-33⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (1)],0⟩⟩,⟨53,8,⟨⟨42,55,-55,-72⟩,[.t (-1),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (1)],0⟩⟩,⟨48,7,⟨⟨-56,-71,71,90⟩,[.t (-1),.s,.t (-5),.s,.t (-4),.s,.t (-4),.s,.t (1)],0⟩⟩,⟨31,5,⟨⟨-8,-9,9,10⟩,[.t (-1),.s,.t (-9),.s,.t (1)],0⟩⟩,⟨36,5,⟨⟨10,9,-9,-8⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨50,7,⟨⟨90,71,-71,-56⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨52,8,⟨⟨-72,-55,55,42⟩,[.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨46,-3,⟨⟨-67,-49,93,68⟩,[.t (-1),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨41,6,⟨⟨-33,-23,23,16⟩,[.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨40,-3,⟨⟨-30,-19,49,31⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨26,3,⟨⟨16,9,-9,-5⟩,[.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨33,4,⟨⟨9,4,-25,-11⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨28,4,⟨⟨-11,-4,25,9⟩,[.t (-1),.s,.t (-2),.s,.t (-5),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨11,2,⟨⟨5,1,-1,0⟩,[.t (-5),.s,.t (0)],0⟩⟩,⟨8,1,⟨⟨3,-1,1,0⟩,[.t (3),.s,.t (0)],0⟩⟩,⟨17,-3,⟨⟨5,-7,3,-4⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨5,1,⟨⟨0,1,-1,3⟩,[.t (0),.s,.t (-3)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-2,1),(-3,2),(-4,3),(-9,7),(-5,4),(-1,1),(-4,5),(-7,9),(-3,4),(-5,7),(-2,3),(-3,5),(-1,2),(-2,5),(-1,3),(0,1),(1,1),(2,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end PSL2_17_c4

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
