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
namespace G216_88_c0
noncomputable def originalSData : LookupTree (Fin 108) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (9)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (12)) (.branch 8 (.leaf (0)) (.leaf (15)))) (.branch 11 (.branch 10 (.leaf (14)) (.leaf (18))) (.branch 12 (.leaf (19)) (.leaf (16)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (17)) (.branch 15 (.leaf (22)) (.leaf (2)))) (.branch 18 (.branch 17 (.leaf (25)) (.leaf (26))) (.branch 19 (.leaf (23)) (.leaf (24))))) (.branch 23 (.branch 21 (.leaf (29)) (.branch 22 (.leaf (30)) (.leaf (4)))) (.branch 25 (.branch 24 (.leaf (33)) (.leaf (34))) (.branch 26 (.leaf (6)) (.leaf (32))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (37)) (.branch 29 (.leaf (39)) (.leaf (35)))) (.branch 31 (.leaf (36)) (.branch 32 (.leaf (41)) (.leaf (13))))) (.branch 36 (.branch 34 (.leaf (10)) (.branch 35 (.leaf (11)) (.leaf (45)))) (.branch 38 (.branch 37 (.leaf (46)) (.leaf (43))) (.branch 39 (.leaf (48)) (.leaf (44)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (50)) (.branch 42 (.leaf (47)) (.leaf (52)))) (.branch 45 (.branch 44 (.leaf (54)) (.leaf (56))) (.branch 46 (.leaf (20)) (.leaf (21))))) (.branch 50 (.branch 48 (.leaf (58)) (.branch 49 (.leaf (55)) (.leaf (61)))) (.branch 52 (.branch 51 (.leaf (57)) (.leaf (64))) (.branch 53 (.leaf (59)) (.leaf (67)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (27)) (.branch 56 (.leaf (69)) (.leaf (28)))) (.branch 58 (.leaf (71)) (.branch 59 (.leaf (31)) (.leaf (73))))) (.branch 63 (.branch 61 (.leaf (75)) (.branch 62 (.leaf (70)) (.leaf (76)))) (.branch 65 (.branch 64 (.leaf (78)) (.leaf (72))) (.branch 66 (.leaf (79)) (.leaf (80)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (74)) (.branch 69 (.leaf (77)) (.leaf (38)))) (.branch 72 (.branch 71 (.leaf (82)) (.leaf (40))) (.branch 73 (.leaf (85)) (.leaf (42))))) (.branch 77 (.branch 75 (.leaf (88)) (.branch 76 (.leaf (81)) (.leaf (83)))) (.branch 79 (.branch 78 (.leaf (89)) (.leaf (84))) (.branch 80 (.leaf (86)) (.leaf (87))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (93)) (.branch 83 (.leaf (49)) (.leaf (94)))) (.branch 85 (.leaf (96)) (.branch 86 (.leaf (51)) (.leaf (97))))) (.branch 90 (.branch 88 (.leaf (98)) (.branch 89 (.leaf (53)) (.leaf (95)))) (.branch 92 (.branch 91 (.leaf (99)) (.leaf (100))) (.branch 93 (.leaf (101)) (.leaf (60)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (62)) (.branch 96 (.leaf (68)) (.leaf (63)))) (.branch 99 (.branch 98 (.leaf (65)) (.leaf (66))) (.branch 100 (.leaf (102)) (.leaf (103))))) (.branch 104 (.branch 102 (.leaf (104)) (.branch 103 (.leaf (105)) (.leaf (106)))) (.branch 106 (.branch 105 (.leaf (107)) (.leaf (90))) (.branch 107 (.leaf (91)) (.leaf (92)))))))))
noncomputable def originalS (p : Fin 108) : Fin 108 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 108) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (10)) (.leaf (11))))) (.branch 9 (.branch 7 (.leaf (13)) (.branch 8 (.leaf (14)) (.leaf (16)))) (.branch 11 (.branch 10 (.leaf (17)) (.leaf (19))) (.branch 12 (.leaf (20)) (.leaf (21)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (0)) (.branch 15 (.leaf (23)) (.leaf (24)))) (.branch 18 (.branch 17 (.leaf (26)) (.leaf (27))) (.branch 19 (.leaf (28)) (.leaf (1))))) (.branch 23 (.branch 21 (.leaf (30)) (.branch 22 (.leaf (31)) (.leaf (32)))) (.branch 25 (.branch 24 (.leaf (34)) (.leaf (35))) (.branch 26 (.leaf (36)) (.leaf (3))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (38)) (.branch 29 (.leaf (40)) (.leaf (33)))) (.branch 31 (.leaf (5)) (.branch 32 (.leaf (42)) (.leaf (43))))) (.branch 36 (.branch 34 (.leaf (44)) (.branch 35 (.leaf (7)) (.leaf (46)))) (.branch 38 (.branch 37 (.leaf (47)) (.leaf (12))) (.branch 39 (.leaf (49)) (.leaf (9)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (51)) (.branch 42 (.leaf (45)) (.leaf (53)))) (.branch 45 (.branch 44 (.leaf (55)) (.leaf (57))) (.branch 46 (.leaf (18)) (.leaf (15))))) (.branch 50 (.branch 48 (.leaf (59)) (.branch 49 (.leaf (60)) (.leaf (62)))) (.branch 52 (.branch 51 (.leaf (63)) (.leaf (65))) (.branch 53 (.leaf (66)) (.leaf (68)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (25)) (.branch 56 (.leaf (70)) (.leaf (22)))) (.branch 58 (.leaf (72)) (.branch 59 (.leaf (29)) (.leaf (74))))) (.branch 63 (.branch 61 (.leaf (69)) (.branch 62 (.leaf (75)) (.leaf (77)))) (.branch 65 (.branch 64 (.leaf (71)) (.leaf (78))) (.branch 66 (.leaf (76)) (.leaf (73)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (80)) (.branch 69 (.leaf (79)) (.leaf (81)))) (.branch 72 (.branch 71 (.leaf (83)) (.leaf (84))) (.branch 73 (.leaf (86)) (.leaf (87))))) (.branch 77 (.branch 75 (.leaf (89)) (.branch 76 (.leaf (37)) (.leaf (90)))) (.branch 79 (.branch 78 (.leaf (91)) (.leaf (39))) (.branch 80 (.leaf (92)) (.leaf (41))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (48)) (.branch 83 (.leaf (93)) (.leaf (95)))) (.branch 85 (.leaf (50)) (.branch 86 (.leaf (96)) (.leaf (94))))) (.branch 90 (.branch 88 (.leaf (52)) (.branch 89 (.leaf (98)) (.leaf (97)))) (.branch 92 (.branch 91 (.leaf (100)) (.leaf (101))) (.branch 93 (.leaf (99)) (.leaf (54)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (102)) (.branch 96 (.leaf (103)) (.leaf (56)))) (.branch 99 (.branch 98 (.leaf (104)) (.leaf (58))) (.branch 100 (.leaf (61)) (.leaf (67))))) (.branch 104 (.branch 102 (.leaf (64)) (.branch 103 (.leaf (106)) (.leaf (107)))) (.branch 106 (.branch 105 (.leaf (105)) (.leaf (82))) (.branch 107 (.leaf (88)) (.leaf (85)))))))))
noncomputable def originalT (p : Fin 108) : Fin 108 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 54) :=
  (.branch 54 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (8)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (10)) (.branch 15 (.leaf (3)) (.leaf (4)))) (.branch 18 (.branch 17 (.leaf (5)) (.leaf (11))) (.branch 19 (.leaf (12)) (.leaf (13))))) (.branch 23 (.branch 21 (.leaf (14)) (.branch 22 (.leaf (15)) (.leaf (6)))) (.branch 25 (.branch 24 (.leaf (7)) (.leaf (8))) (.branch 26 (.leaf (9)) (.leaf (10))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (16)) (.branch 29 (.leaf (17)) (.leaf (18)))) (.branch 31 (.leaf (19)) (.branch 32 (.leaf (20)) (.leaf (11))))) (.branch 36 (.branch 34 (.leaf (12)) (.branch 35 (.leaf (13)) (.leaf (14)))) (.branch 38 (.branch 37 (.leaf (15)) (.leaf (21))) (.branch 39 (.leaf (22)) (.leaf (23)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (24)) (.branch 42 (.leaf (25)) (.leaf (26)))) (.branch 45 (.branch 44 (.leaf (16)) (.leaf (17))) (.branch 46 (.leaf (18)) (.leaf (19))))) (.branch 50 (.branch 48 (.leaf (20)) (.branch 49 (.leaf (27)) (.leaf (28)))) (.branch 52 (.branch 51 (.leaf (29)) (.leaf (30))) (.branch 53 (.leaf (31)) (.leaf (32)))))))) (.branch 81 (.branch 67 (.branch 60 (.branch 57 (.branch 55 (.leaf (21)) (.branch 56 (.leaf (22)) (.leaf (23)))) (.branch 58 (.leaf (24)) (.branch 59 (.leaf (25)) (.leaf (26))))) (.branch 63 (.branch 61 (.leaf (33)) (.branch 62 (.leaf (34)) (.leaf (35)))) (.branch 65 (.branch 64 (.leaf (36)) (.leaf (37))) (.branch 66 (.leaf (38)) (.leaf (39)))))) (.branch 74 (.branch 70 (.branch 68 (.leaf (40)) (.branch 69 (.leaf (41)) (.leaf (27)))) (.branch 72 (.branch 71 (.leaf (28)) (.leaf (29))) (.branch 73 (.leaf (30)) (.leaf (31))))) (.branch 77 (.branch 75 (.leaf (32)) (.branch 76 (.leaf (42)) (.leaf (43)))) (.branch 79 (.branch 78 (.leaf (44)) (.leaf (45))) (.branch 80 (.leaf (46)) (.leaf (47))))))) (.branch 94 (.branch 87 (.branch 84 (.branch 82 (.leaf (33)) (.branch 83 (.leaf (34)) (.leaf (35)))) (.branch 85 (.leaf (36)) (.branch 86 (.leaf (37)) (.leaf (38))))) (.branch 90 (.branch 88 (.leaf (39)) (.branch 89 (.leaf (40)) (.leaf (41)))) (.branch 92 (.branch 91 (.leaf (48)) (.leaf (49))) (.branch 93 (.leaf (50)) (.leaf (42)))))) (.branch 101 (.branch 97 (.branch 95 (.leaf (43)) (.branch 96 (.leaf (44)) (.leaf (45)))) (.branch 99 (.branch 98 (.leaf (46)) (.leaf (47))) (.branch 100 (.leaf (51)) (.leaf (52))))) (.branch 104 (.branch 102 (.leaf (53)) (.branch 103 (.leaf (48)) (.leaf (49)))) (.branch 106 (.branch 105 (.leaf (50)) (.leaf (51))) (.branch 107 (.leaf (52)) (.leaf (53)))))))))
noncomputable def projection (p : Fin 108) : Fin 54 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 108) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (11)))) (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (17)) (.leaf (18)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (19)) (.branch 15 (.leaf (20)) (.leaf (21)))) (.branch 18 (.branch 17 (.leaf (27)) (.leaf (28))) (.branch 19 (.leaf (29)) (.leaf (30))))) (.branch 23 (.branch 21 (.leaf (31)) (.branch 22 (.leaf (37)) (.leaf (38)))) (.branch 25 (.branch 24 (.leaf (39)) (.leaf (40))) (.branch 26 (.leaf (41)) (.leaf (42))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (48)) (.branch 29 (.leaf (49)) (.leaf (50)))) (.branch 31 (.leaf (51)) (.branch 32 (.leaf (52)) (.leaf (53))))) (.branch 36 (.branch 34 (.leaf (60)) (.branch 35 (.leaf (61)) (.leaf (62)))) (.branch 38 (.branch 37 (.leaf (63)) (.leaf (64))) (.branch 39 (.leaf (65)) (.leaf (66)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (67)) (.branch 42 (.leaf (68)) (.leaf (75)))) (.branch 45 (.branch 44 (.leaf (76)) (.leaf (77))) (.branch 46 (.leaf (78)) (.leaf (79))))) (.branch 50 (.branch 48 (.leaf (80)) (.branch 49 (.leaf (90)) (.leaf (91)))) (.branch 52 (.branch 51 (.leaf (92)) (.leaf (99))) (.branch 53 (.leaf (100)) (.leaf (101))))))))
noncomputable def representative (p : Fin 54) : Fin 108 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (13)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (11))) (.branch 12 (.leaf (10)) (.leaf (7)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (18)) (.leaf (19)))) (.branch 18 (.branch 17 (.leaf (21)) (.leaf (23))) (.branch 19 (.leaf (14)) (.leaf (15))))) (.branch 23 (.branch 21 (.leaf (25)) (.branch 22 (.leaf (16)) (.leaf (27)))) (.branch 25 (.branch 24 (.leaf (17)) (.leaf (29))) (.branch 26 (.leaf (20)) (.leaf (31))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (22)) (.branch 29 (.leaf (34)) (.leaf (24)))) (.branch 31 (.leaf (37)) (.branch 32 (.leaf (26)) (.leaf (40))))) (.branch 36 (.branch 34 (.leaf (42)) (.branch 35 (.leaf (28)) (.leaf (43)))) (.branch 38 (.branch 37 (.leaf (45)) (.leaf (30))) (.branch 39 (.leaf (46)) (.leaf (47)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (32)) (.branch 42 (.leaf (44)) (.leaf (33)))) (.branch 45 (.branch 44 (.leaf (35)) (.leaf (41))) (.branch 46 (.leaf (36)) (.leaf (38))))) (.branch 50 (.branch 48 (.leaf (39)) (.branch 49 (.leaf (51)) (.leaf (52)))) (.branch 52 (.branch 51 (.leaf (53)) (.leaf (48))) (.branch 53 (.leaf (49)) (.leaf (50))))))))
noncomputable def S (p : Fin 54) : Fin 54 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (8)) (.leaf (10))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (14)))) (.branch 11 (.branch 10 (.leaf (15)) (.leaf (0))) (.branch 12 (.leaf (16)) (.leaf (17)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (1)) (.branch 15 (.leaf (19)) (.leaf (20)))) (.branch 18 (.branch 17 (.leaf (22)) (.leaf (24))) (.branch 19 (.leaf (12)) (.leaf (4))))) (.branch 23 (.branch 21 (.leaf (26)) (.branch 22 (.leaf (9)) (.leaf (28)))) (.branch 25 (.branch 24 (.leaf (6)) (.leaf (30))) (.branch 26 (.leaf (18)) (.leaf (32))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (33)) (.branch 29 (.leaf (35)) (.leaf (36)))) (.branch 31 (.leaf (38)) (.branch 32 (.leaf (39)) (.leaf (41))))) (.branch 36 (.branch 34 (.leaf (27)) (.branch 35 (.leaf (42)) (.leaf (44)))) (.branch 38 (.branch 37 (.leaf (29)) (.leaf (45))) (.branch 39 (.leaf (43)) (.leaf (31)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (47)) (.branch 42 (.leaf (46)) (.leaf (21)))) (.branch 45 (.branch 44 (.leaf (48)) (.leaf (49))) (.branch 46 (.leaf (23)) (.leaf (50))))) (.branch 50 (.branch 48 (.leaf (25)) (.branch 49 (.leaf (52)) (.leaf (53)))) (.branch 52 (.branch 51 (.leaf (51)) (.leaf (34))) (.branch 53 (.leaf (40)) (.leaf (37))))))))
noncomputable def T (p : Fin 54) : Fin 54 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 54) :=
  (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (10)) (.branch 2 (.leaf (13)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (19)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (23)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (21)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (18)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (8)) (.leaf (9)))) (.branch 18 (.branch 17 (.leaf (11)) (.leaf (12))) (.branch 19 (.leaf (25)) (.leaf (14))))) (.branch 23 (.branch 21 (.leaf (15)) (.branch 22 (.leaf (42)) (.leaf (16)))) (.branch 25 (.branch 24 (.leaf (45)) (.leaf (17))) (.branch 26 (.leaf (47)) (.leaf (20))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (33)) (.branch 29 (.leaf (22)) (.leaf (36)))) (.branch 31 (.leaf (24)) (.branch 32 (.leaf (39)) (.leaf (26))))) (.branch 36 (.branch 34 (.leaf (27)) (.branch 35 (.leaf (51)) (.leaf (28)))) (.branch 38 (.branch 37 (.leaf (29)) (.leaf (53))) (.branch 39 (.leaf (30)) (.leaf (31)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (52)) (.branch 42 (.leaf (32)) (.leaf (34)))) (.branch 45 (.branch 44 (.leaf (38)) (.leaf (35))) (.branch 46 (.leaf (37)) (.leaf (41))))) (.branch 50 (.branch 48 (.leaf (40)) (.branch 49 (.leaf (43)) (.leaf (44)))) (.branch 52 (.branch 51 (.leaf (46)) (.leaf (50))) (.branch 53 (.leaf (48)) (.leaf (49))))))))
noncomputable def Ti (p : Fin 54) : Fin 54 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 54) : Fin 54 := T (S p)
theorem quotient_relations : (∀ p : Fin 54, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 108, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 108, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 54, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 54)) := [[0,3,11],[1,2,8],[4,5,15],[6,7,17],[9,10,16],[12,13,14],[18,19,20],[21,22,33],[23,24,36],[25,26,39],[27,28,42],[29,30,45],[31,32,47],[34,35,48],[37,38,50],[40,41,49],[43,44,46],[51,52,53]]
noncomputable def verticesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (2)) (.leaf (15)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (16)) (.branch 15 (.leaf (17)) (.leaf (8)))) (.branch 18 (.branch 17 (.leaf (14)) (.leaf (11))) (.branch 19 (.leaf (18)) (.leaf (19))))) (.branch 23 (.branch 21 (.leaf (20)) (.branch 22 (.leaf (21)) (.leaf (22)))) (.branch 25 (.branch 24 (.leaf (24)) (.leaf (25))) (.branch 26 (.leaf (27)) (.leaf (28))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (30)) (.branch 29 (.leaf (31)) (.leaf (33)))) (.branch 31 (.leaf (34)) (.branch 32 (.leaf (36)) (.leaf (37))))) (.branch 36 (.branch 34 (.leaf (23)) (.branch 35 (.leaf (39)) (.leaf (40)))) (.branch 38 (.branch 37 (.leaf (26)) (.leaf (42))) (.branch 39 (.leaf (43)) (.leaf (29)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (45)) (.branch 42 (.leaf (46)) (.leaf (32)))) (.branch 45 (.branch 44 (.leaf (48)) (.leaf (49))) (.branch 46 (.leaf (35)) (.leaf (50))))) (.branch 50 (.branch 48 (.leaf (38)) (.branch 49 (.leaf (41)) (.leaf (47)))) (.branch 52 (.branch 51 (.leaf (44)) (.leaf (51))) (.branch 53 (.leaf (52)) (.leaf (53))))))))
noncomputable def verticesIndex (p : Fin 54) : Fin 54 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (11)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (15)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (17)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (10)) (.branch 15 (.leaf (16)) (.leaf (12)))) (.branch 18 (.branch 17 (.leaf (13)) (.leaf (14))) (.branch 19 (.leaf (18)) (.leaf (19))))) (.branch 23 (.branch 21 (.leaf (20)) (.branch 22 (.leaf (21)) (.leaf (22)))) (.branch 25 (.branch 24 (.leaf (33)) (.leaf (23))) (.branch 26 (.leaf (24)) (.leaf (36))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (25)) (.branch 29 (.leaf (26)) (.leaf (39)))) (.branch 31 (.leaf (27)) (.branch 32 (.leaf (28)) (.leaf (42))))) (.branch 36 (.branch 34 (.leaf (29)) (.branch 35 (.leaf (30)) (.leaf (45)))) (.branch 38 (.branch 37 (.leaf (31)) (.leaf (32))) (.branch 39 (.leaf (47)) (.leaf (34)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (35)) (.branch 42 (.leaf (48)) (.leaf (37)))) (.branch 45 (.branch 44 (.leaf (38)) (.leaf (50))) (.branch 46 (.leaf (40)) (.leaf (41))))) (.branch 50 (.branch 48 (.leaf (49)) (.branch 49 (.leaf (43)) (.leaf (44)))) (.branch 52 (.branch 51 (.leaf (46)) (.leaf (51))) (.branch 53 (.leaf (52)) (.leaf (53))))))))
noncomputable def verticesBack (p : Fin 54) : Fin 54 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 54, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 54 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 54, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 54)) := [[0,1],[2,4],[3,6],[5,9],[7,12],[8,13],[10,11],[14,18],[15,19],[16,21],[17,23],[20,25],[22,27],[24,29],[26,31],[28,34],[30,37],[32,40],[33,42],[35,43],[36,45],[38,46],[39,47],[41,44],[48,51],[49,52],[50,53]]
noncomputable def edgesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (10)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (12))) (.branch 12 (.leaf (13)) (.leaf (9)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (11)) (.branch 15 (.leaf (14)) (.leaf (16)))) (.branch 18 (.branch 17 (.leaf (18)) (.leaf (20))) (.branch 19 (.leaf (15)) (.leaf (17))))) (.branch 23 (.branch 21 (.leaf (22)) (.branch 22 (.leaf (19)) (.leaf (24)))) (.branch 25 (.branch 24 (.leaf (21)) (.leaf (26))) (.branch 26 (.leaf (23)) (.leaf (28))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (25)) (.branch 29 (.leaf (30)) (.leaf (27)))) (.branch 31 (.leaf (32)) (.branch 32 (.leaf (29)) (.leaf (34))))) (.branch 36 (.branch 34 (.leaf (36)) (.branch 35 (.leaf (31)) (.leaf (38)))) (.branch 38 (.branch 37 (.leaf (40)) (.leaf (33))) (.branch 39 (.leaf (42)) (.leaf (44)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (35)) (.branch 42 (.leaf (46)) (.leaf (37)))) (.branch 45 (.branch 44 (.leaf (39)) (.leaf (47))) (.branch 46 (.leaf (41)) (.leaf (43))))) (.branch 50 (.branch 48 (.leaf (45)) (.branch 49 (.leaf (48)) (.leaf (50)))) (.branch 52 (.branch 51 (.leaf (52)) (.leaf (49))) (.branch 53 (.leaf (51)) (.leaf (53))))))))
noncomputable def edgesIndex (p : Fin 54) : Fin 54 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (12)) (.leaf (8))) (.branch 12 (.leaf (13)) (.leaf (10)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (11)) (.branch 15 (.leaf (14)) (.leaf (18)))) (.branch 18 (.branch 17 (.leaf (15)) (.leaf (19))) (.branch 19 (.leaf (16)) (.leaf (21))))) (.branch 23 (.branch 21 (.leaf (17)) (.branch 22 (.leaf (23)) (.leaf (20)))) (.branch 25 (.branch 24 (.leaf (25)) (.leaf (22))) (.branch 26 (.leaf (27)) (.leaf (24))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (29)) (.branch 29 (.leaf (26)) (.leaf (31)))) (.branch 31 (.leaf (28)) (.branch 32 (.leaf (34)) (.leaf (30))))) (.branch 36 (.branch 34 (.leaf (37)) (.branch 35 (.leaf (32)) (.leaf (40)))) (.branch 38 (.branch 37 (.leaf (33)) (.leaf (42))) (.branch 39 (.leaf (35)) (.leaf (43)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (36)) (.branch 42 (.leaf (45)) (.leaf (38)))) (.branch 45 (.branch 44 (.leaf (46)) (.leaf (39))) (.branch 46 (.leaf (47)) (.leaf (41))))) (.branch 50 (.branch 48 (.leaf (44)) (.branch 49 (.leaf (48)) (.leaf (51)))) (.branch 52 (.branch 51 (.leaf (49)) (.leaf (52))) (.branch 53 (.leaf (50)) (.leaf (53))))))))
noncomputable def edgesBack (p : Fin 54) : Fin 54 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 54, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 54 := by decide +kernel
theorem edges_partition : ∀ p : Fin 54, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 54)) := [[0,2,5,10],[1,3,7,13],[4,8,14,19],[6,11,16,22,28,35,44,49,53,37,45,23],[9,15,20,26,32,41,46,50,51,34,42,21],[12,17,24,30,38,43,48,52,40,47,25,18],[27,33],[29,36],[31,39]]
noncomputable def facesIndexData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (8)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (12)) (.branch 8 (.leaf (6)) (.leaf (9)))) (.branch 11 (.branch 10 (.leaf (24)) (.leaf (3))) (.branch 12 (.leaf (13)) (.leaf (36)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (7)) (.branch 15 (.leaf (10)) (.leaf (25)))) (.branch 18 (.branch 17 (.leaf (14)) (.leaf (37))) (.branch 19 (.leaf (47)) (.leaf (11))))) (.branch 23 (.branch 21 (.leaf (26)) (.branch 22 (.leaf (35)) (.leaf (15)))) (.branch 25 (.branch 24 (.leaf (23)) (.leaf (38))) (.branch 26 (.leaf (46)) (.leaf (27))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (48)) (.branch 29 (.leaf (16)) (.leaf (50)))) (.branch 31 (.leaf (39)) (.branch 32 (.leaf (52)) (.leaf (28))))) (.branch 36 (.branch 34 (.leaf (49)) (.branch 35 (.leaf (33)) (.leaf (17)))) (.branch 38 (.branch 37 (.leaf (51)) (.leaf (21))) (.branch 39 (.leaf (40)) (.leaf (53)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (44)) (.branch 42 (.leaf (29)) (.leaf (34)))) (.branch 45 (.branch 44 (.leaf (41)) (.leaf (18))) (.branch 46 (.leaf (22)) (.leaf (30))))) (.branch 50 (.branch 48 (.leaf (45)) (.branch 49 (.leaf (42)) (.leaf (19)))) (.branch 52 (.branch 51 (.leaf (31)) (.leaf (32))) (.branch 53 (.leaf (43)) (.leaf (20))))))))
noncomputable def facesIndex (p : Fin 54) : Fin 54 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 54) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (10)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (13)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (14))) (.branch 12 (.leaf (19)) (.leaf (6)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (11)) (.branch 15 (.leaf (16)) (.leaf (22)))) (.branch 18 (.branch 17 (.leaf (28)) (.leaf (35))) (.branch 19 (.leaf (44)) (.leaf (49))))) (.branch 23 (.branch 21 (.leaf (53)) (.branch 22 (.leaf (37)) (.leaf (45)))) (.branch 25 (.branch 24 (.leaf (23)) (.leaf (9))) (.branch 26 (.leaf (15)) (.leaf (20))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (26)) (.branch 29 (.leaf (32)) (.leaf (41)))) (.branch 31 (.leaf (46)) (.branch 32 (.leaf (50)) (.leaf (51))))) (.branch 36 (.branch 34 (.leaf (34)) (.branch 35 (.leaf (42)) (.leaf (21)))) (.branch 38 (.branch 37 (.leaf (12)) (.leaf (17))) (.branch 39 (.leaf (24)) (.leaf (30)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (38)) (.branch 42 (.leaf (43)) (.leaf (48)))) (.branch 45 (.branch 44 (.leaf (52)) (.leaf (40))) (.branch 46 (.leaf (47)) (.leaf (25))))) (.branch 50 (.branch 48 (.leaf (18)) (.branch 49 (.leaf (27)) (.leaf (33)))) (.branch 52 (.branch 51 (.leaf (29)) (.leaf (36))) (.branch 53 (.leaf (31)) (.leaf (39))))))))
noncomputable def facesBack (p : Fin 54) : Fin 54 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 54, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 54 := by decide +kernel
theorem faces_partition : ∀ p : Fin 54, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [4,4,4,12,12,12,2,2,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 1 : Int) = 18 - 27 + 9 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 27 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))) (.branch 11 (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.leaf (⟨-1,-3,0,-1⟩))) (.branch 12 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,0,2,1⟩)))))) (.branch 20 (.branch 16 (.branch 14 (.leaf (⟨0,1,-1,1⟩)) (.branch 15 (.leaf (⟨1,1,1,2⟩)) (.leaf (⟨2,1,1,1⟩)))) (.branch 18 (.branch 17 (.leaf (⟨-3,-2,-1,-1⟩)) (.leaf (⟨1,1,-2,-1⟩))) (.branch 19 (.leaf (⟨-3,-1,-2,-1⟩)) (.leaf (⟨1,-2,1,-1⟩))))) (.branch 23 (.branch 21 (.leaf (⟨-2,-3,-1,-2⟩)) (.branch 22 (.leaf (⟨-2,3,-1,1⟩)) (.leaf (⟨3,5,1,2⟩)))) (.branch 25 (.branch 24 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-2,2,3⟩))) (.branch 26 (.leaf (⟨-3,2,-2,1⟩)) (.leaf (⟨2,5,1,3⟩))))))) (.branch 40 (.branch 33 (.branch 30 (.branch 28 (.leaf (⟨5,-3,2,-1⟩)) (.branch 29 (.leaf (⟨-3,-8,-1,-3⟩)) (.leaf (⟨-2,1,3,-2⟩)))) (.branch 31 (.leaf (⟨1,3,-2,-5⟩)) (.branch 32 (.leaf (⟨5,-2,3,-1⟩)) (.leaf (⟨-2,-7,-1,-4⟩))))) (.branch 36 (.branch 34 (.leaf (⟨5,2,2,1⟩)) (.branch 35 (.leaf (⟨-8,3,-3,1⟩)) (.leaf (⟨3,11,1,4⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-2,-1,3,1⟩)) (.leaf (⟨3,-1,-5,2⟩))) (.branch 39 (.leaf (⟨-1,-4,2,7⟩)) (.leaf (⟨5,3,3,2⟩)))))) (.branch 47 (.branch 43 (.branch 41 (.leaf (⟨-7,2,-4,1⟩)) (.branch 42 (.leaf (⟨2,9,1,5⟩)) (.leaf (⟨-8,-5,-3,-2⟩)))) (.branch 45 (.branch 44 (.leaf (⟨11,-3,4,-1⟩)) (.leaf (⟨-3,-14,-1,-5⟩))) (.branch 46 (.leaf (⟨3,2,-5,-3⟩)) (.leaf (⟨-14,-11,-5,-4⟩))))) (.branch 50 (.branch 48 (.leaf (⟨-7,-5,-4,-3⟩)) (.branch 49 (.leaf (⟨11,8,4,3⟩)) (.leaf (⟨9,7,5,4⟩)))) (.branch 52 (.branch 51 (.leaf (⟨-4,-3,7,5⟩)) (.leaf (⟨8,-11,3,-4⟩))) (.branch 53 (.leaf (⟨-11,-19,-4,-7⟩)) (.leaf (⟨-19,-8,-7,-3⟩))))))))
noncomputable def liftMatrix (p : Fin 54) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 54) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],13⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],14⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],15⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],16⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],17⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],18⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],19⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],20⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],21⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],22⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],23⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],24⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],25⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],26⟩,⟨⟨5,-3,2,-1⟩,[.t (2),.s,.t (-2),.s,.t (-1)],27⟩,⟨⟨-3,-8,-1,-3⟩,[.t (3),.s,.t (3)],28⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],29⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],30⟩,⟨⟨5,-2,3,-1⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],31⟩,⟨⟨-2,-7,-1,-4⟩,[.t (2),.s,.t (4)],32⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],33⟩,⟨⟨-8,3,-3,1⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],34⟩,⟨⟨3,11,1,4⟩,[.t (3),.s,.t (4)],35⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],36⟩,⟨⟨3,-1,-5,2⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-1)],37⟩,⟨⟨-1,-4,2,7⟩,[.t (-1),.s,.t (-2),.s,.t (3)],38⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],39⟩,⟨⟨-7,2,-4,1⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],40⟩,⟨⟨2,9,1,5⟩,[.t (2),.s,.t (5)],41⟩,⟨⟨-8,-5,-3,-2⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (0)],42⟩,⟨⟨11,-3,4,-1⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],43⟩,⟨⟨-3,-14,-1,-5⟩,[.t (3),.s,.t (5)],44⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],45⟩,⟨⟨-14,-11,-5,-4⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],46⟩,⟨⟨-7,-5,-4,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],47⟩,⟨⟨11,8,4,3⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],48⟩,⟨⟨9,7,5,4⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],49⟩,⟨⟨-4,-3,7,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],50⟩,⟨⟨8,-11,3,-4⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],51⟩,⟨⟨-11,-19,-4,-7⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],52⟩,⟨⟨-19,-8,-7,-3⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],53⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 54 ∧ ((List.finRange 54).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 54) := [⟨11,2,⟨⟨1,4,0,1⟩,[.t (4)],0⟩⟩,⟨36,5,⟨⟨11,8,-18,-13⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨45,5,⟨⟨-13,-8,18,11⟩,[.t (-1),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨50,10,⟨⟨-173,-100,-64,-37⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-4),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨38,6,⟨⟨-105,-58,-38,-21⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,1,⟨⟨-1,0,-4,-1⟩,[.t (0),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨12,1,⟨⟨-1,0,4,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨14,3,⟨⟨-5,4,-4,3⟩,[.t (1),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨18,3,⟨⟨3,-4,4,-5⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨39,7,⟨⟨-31,50,-18,29⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨47,7,⟨⟨29,-50,18,-31⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-2)],0⟩⟩,⟨49,9,⟨⟨-131,232,-48,85⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-5),.s,.t (-2)],0⟩⟩,⟨41,8,⟨⟨-73,132,-26,47⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-6),.s,.t (-2)],0⟩⟩,⟨33,4,⟨⟨-21,50,-8,19⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨42,4,⟨⟨19,-50,8,-21⟩,[.t (2),.s,.t (-3),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨53,10,⟨⟨-37,100,64,-173⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨52,9,⟨⟨85,-232,48,-131⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨46,6,⟨⟨-21,58,38,-105⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-3)],0⟩⟩,⟨44,8,⟨⟨47,-132,26,-73⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-6),.s,.t (-3)],0⟩⟩,⟨10,2,⟨⟨1,-4,0,1⟩,[.t (-4)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-2,3),(-3,5),(-4,7),(-1,2),(0,1),(1,2),(1,1),(3,2),(5,3),(7,4),(9,5),(2,1),(5,2),(8,3),(19,7),(11,4),(14,5),(3,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G216_88_c0

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
