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
namespace A7_c14
noncomputable def originalSData : LookupTree (Fin 96) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (9)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (12)) (.branch 8 (.leaf (0)) (.leaf (15)))) (.branch 10 (.leaf (14)) (.branch 11 (.leaf (18)) (.leaf (19)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (16)) (.branch 14 (.leaf (22)) (.leaf (24)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (27)) (.leaf (29))))) (.branch 21 (.branch 19 (.leaf (25)) (.branch 20 (.leaf (26)) (.leaf (32)))) (.branch 22 (.leaf (33)) (.branch 23 (.leaf (28)) (.leaf (36))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (4)) (.branch 26 (.leaf (39)) (.leaf (40)))) (.branch 28 (.leaf (6)) (.branch 29 (.leaf (43)) (.leaf (38))))) (.branch 33 (.branch 31 (.leaf (45)) (.branch 32 (.leaf (30)) (.leaf (41)))) (.branch 34 (.leaf (42)) (.branch 35 (.leaf (47)) (.leaf (49)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (44)) (.branch 38 (.leaf (17)) (.leaf (37)))) (.branch 40 (.leaf (10)) (.branch 41 (.leaf (11)) (.leaf (53))))) (.branch 45 (.branch 43 (.leaf (54)) (.branch 44 (.leaf (13)) (.leaf (46)))) (.branch 46 (.leaf (52)) (.branch 47 (.leaf (23)) (.leaf (55)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (58)) (.branch 50 (.leaf (56)) (.leaf (60)))) (.branch 52 (.leaf (62)) (.branch 53 (.leaf (31)) (.leaf (20))))) (.branch 57 (.branch 55 (.leaf (21)) (.branch 56 (.leaf (64)) (.leaf (66)))) (.branch 58 (.leaf (68)) (.branch 59 (.leaf (65)) (.leaf (71)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (67)) (.branch 62 (.leaf (74)) (.leaf (57)))) (.branch 64 (.leaf (70)) (.branch 65 (.leaf (34)) (.leaf (75))))) (.branch 69 (.branch 67 (.leaf (35)) (.branch 68 (.leaf (77)) (.leaf (51)))) (.branch 70 (.leaf (79)) (.branch 71 (.leaf (69)) (.leaf (76))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (82)) (.branch 74 (.leaf (72)) (.leaf (78)))) (.branch 76 (.leaf (48)) (.branch 77 (.leaf (85)) (.leaf (50))))) (.branch 81 (.branch 79 (.leaf (80)) (.branch 80 (.leaf (63)) (.leaf (61)))) (.branch 82 (.leaf (88)) (.branch 83 (.leaf (86)) (.leaf (91)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (92)) (.branch 86 (.leaf (59)) (.leaf (73)))) (.branch 88 (.leaf (95)) (.branch 89 (.leaf (94)) (.leaf (83))))) (.branch 93 (.branch 91 (.leaf (89)) (.branch 92 (.leaf (90)) (.leaf (87)))) (.branch 94 (.leaf (81)) (.branch 95 (.leaf (93)) (.leaf (84)))))))))
noncomputable def originalS (p : Fin 96) : Fin 96 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 96) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (10)) (.leaf (11))))) (.branch 9 (.branch 7 (.leaf (13)) (.branch 8 (.leaf (14)) (.leaf (16)))) (.branch 10 (.leaf (17)) (.branch 11 (.leaf (19)) (.leaf (20)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (21)) (.branch 14 (.leaf (23)) (.leaf (25)))) (.branch 16 (.leaf (26)) (.branch 17 (.leaf (28)) (.leaf (30))))) (.branch 21 (.branch 19 (.leaf (31)) (.branch 20 (.leaf (1)) (.leaf (33)))) (.branch 22 (.leaf (34)) (.branch 23 (.leaf (35)) (.leaf (37))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (38)) (.branch 26 (.leaf (40)) (.leaf (41)))) (.branch 28 (.leaf (42)) (.branch 29 (.leaf (44)) (.leaf (3))))) (.branch 33 (.branch 31 (.leaf (9)) (.branch 32 (.leaf (46)) (.leaf (39)))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (48)) (.leaf (50)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (51)) (.branch 38 (.leaf (0)) (.leaf (52)))) (.branch 40 (.leaf (45)) (.branch 41 (.leaf (7)) (.leaf (54))))) (.branch 45 (.branch 43 (.leaf (55)) (.branch 44 (.leaf (56)) (.leaf (29)))) (.branch 46 (.leaf (36)) (.branch 47 (.leaf (57)) (.leaf (53)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (59)) (.branch 50 (.leaf (12)) (.leaf (61)))) (.branch 52 (.leaf (63)) (.branch 53 (.leaf (24)) (.leaf (18))))) (.branch 57 (.branch 55 (.leaf (15)) (.branch 56 (.leaf (65)) (.leaf (67)))) (.branch 58 (.leaf (69)) (.branch 59 (.leaf (70)) (.leaf (72)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (73)) (.branch 62 (.leaf (62)) (.leaf (22)))) (.branch 64 (.leaf (64)) (.branch 65 (.leaf (32)) (.leaf (76))))) (.branch 69 (.branch 67 (.leaf (27)) (.branch 68 (.leaf (78)) (.leaf (43)))) (.branch 70 (.leaf (47)) (.branch 71 (.leaf (80)) (.leaf (81))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (49)) (.branch 74 (.leaf (83)) (.leaf (84)))) (.branch 76 (.leaf (79)) (.branch 77 (.leaf (86)) (.leaf (82))))) (.branch 81 (.branch 79 (.leaf (68)) (.branch 80 (.leaf (74)) (.leaf (87)))) (.branch 82 (.leaf (89)) (.branch 83 (.leaf (90)) (.leaf (92)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (93)) (.branch 86 (.leaf (94)) (.leaf (66)))) (.branch 88 (.leaf (88)) (.branch 89 (.leaf (58)) (.leaf (71))))) (.branch 93 (.branch 91 (.leaf (95)) (.branch 92 (.leaf (85)) (.leaf (60)))) (.branch 94 (.leaf (75)) (.branch 95 (.leaf (91)) (.leaf (77)))))))))
noncomputable def originalT (p : Fin 96) : Fin 96 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 48) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (3)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (5)) (.leaf (11))))) (.branch 21 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (13)) (.leaf (14)))) (.branch 22 (.leaf (15)) (.branch 23 (.leaf (16)) (.leaf (17))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 28 (.leaf (9)) (.branch 29 (.leaf (10)) (.leaf (18))))) (.branch 33 (.branch 31 (.leaf (19)) (.branch 32 (.leaf (20)) (.leaf (21)))) (.branch 34 (.leaf (22)) (.branch 35 (.leaf (23)) (.leaf (24)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (25)) (.branch 38 (.leaf (18)) (.leaf (11)))) (.branch 40 (.leaf (12)) (.branch 41 (.leaf (13)) (.leaf (14))))) (.branch 45 (.branch 43 (.leaf (15)) (.branch 44 (.leaf (16)) (.leaf (17)))) (.branch 46 (.leaf (20)) (.branch 47 (.leaf (25)) (.leaf (26)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (27)) (.branch 50 (.leaf (28)) (.leaf (29)))) (.branch 52 (.leaf (30)) (.branch 53 (.leaf (19)) (.leaf (21))))) (.branch 57 (.branch 55 (.leaf (22)) (.branch 56 (.leaf (23)) (.leaf (24)))) (.branch 58 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (33)) (.branch 62 (.leaf (34)) (.leaf (35)))) (.branch 64 (.leaf (36)) (.branch 65 (.leaf (26)) (.leaf (27))))) (.branch 69 (.branch 67 (.leaf (28)) (.branch 68 (.leaf (29)) (.leaf (35)))) (.branch 70 (.leaf (36)) (.branch 71 (.leaf (37)) (.leaf (38))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (39)) (.branch 74 (.leaf (40)) (.leaf (41)))) (.branch 76 (.leaf (31)) (.branch 77 (.leaf (32)) (.leaf (33))))) (.branch 81 (.branch 79 (.leaf (34)) (.branch 80 (.leaf (37)) (.leaf (41)))) (.branch 82 (.leaf (42)) (.branch 83 (.leaf (40)) (.leaf (43)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (44)) (.branch 86 (.leaf (38)) (.leaf (39)))) (.branch 88 (.leaf (44)) (.branch 89 (.leaf (45)) (.leaf (46))))) (.branch 93 (.branch 91 (.leaf (43)) (.branch 92 (.leaf (46)) (.leaf (47)))) (.branch 94 (.leaf (45)) (.branch 95 (.leaf (42)) (.leaf (47)))))))))
noncomputable def projection (p : Fin 96) : Fin 48 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 96) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (11)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (13)) (.leaf (17)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (18)) (.branch 14 (.leaf (19)) (.leaf (20)))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (22)) (.leaf (23))))) (.branch 21 (.branch 19 (.leaf (29)) (.branch 20 (.leaf (30)) (.leaf (31)))) (.branch 22 (.leaf (32)) (.branch 23 (.leaf (33)) (.leaf (34))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (35)) (.branch 26 (.leaf (36)) (.leaf (47)))) (.branch 28 (.leaf (48)) (.branch 29 (.leaf (49)) (.leaf (50))))) (.branch 33 (.branch 31 (.leaf (51)) (.branch 32 (.leaf (58)) (.leaf (59)))) (.branch 34 (.leaf (60)) (.branch 35 (.leaf (61)) (.leaf (62)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (63)) (.branch 38 (.leaf (70)) (.leaf (71)))) (.branch 40 (.leaf (72)) (.branch 41 (.leaf (73)) (.leaf (74))))) (.branch 45 (.branch 43 (.leaf (81)) (.branch 44 (.leaf (83)) (.leaf (84)))) (.branch 46 (.leaf (88)) (.branch 47 (.leaf (89)) (.leaf (92))))))))
noncomputable def representative (p : Fin 48) : Fin 96 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (13)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (16)) (.leaf (18)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (21)))) (.branch 16 (.leaf (22)) (.branch 17 (.leaf (10)) (.leaf (25))))) (.branch 21 (.branch 19 (.leaf (11)) (.branch 20 (.leaf (20)) (.leaf (19)))) (.branch 22 (.leaf (14)) (.branch 23 (.leaf (15)) (.leaf (26))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (28)) (.branch 26 (.leaf (17)) (.leaf (23)))) (.branch 28 (.leaf (31)) (.branch 29 (.leaf (24)) (.leaf (33))))) (.branch 33 (.branch 31 (.leaf (35)) (.branch 32 (.leaf (27)) (.leaf (38)))) (.branch 34 (.leaf (29)) (.branch 35 (.leaf (41)) (.leaf (30)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (37)) (.branch 38 (.leaf (36)) (.leaf (32)))) (.branch 40 (.leaf (40)) (.branch 41 (.leaf (39)) (.leaf (34))))) (.branch 45 (.branch 43 (.leaf (45)) (.branch 44 (.leaf (46)) (.leaf (47)))) (.branch 46 (.leaf (42)) (.branch 47 (.leaf (43)) (.leaf (44))))))))
noncomputable def S (p : Fin 48) : Fin 48 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (8)) (.leaf (10))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (14)))) (.branch 10 (.leaf (15)) (.branch 11 (.leaf (17)) (.leaf (19)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (20)) (.branch 14 (.leaf (1)) (.leaf (22)))) (.branch 16 (.leaf (23)) (.branch 17 (.leaf (24)) (.leaf (18))))) (.branch 21 (.branch 19 (.leaf (0)) (.branch 20 (.leaf (6)) (.leaf (25)))) (.branch 22 (.leaf (12)) (.branch 23 (.leaf (4)) (.leaf (27))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (29)) (.branch 26 (.leaf (30)) (.leaf (21)))) (.branch 28 (.leaf (32)) (.branch 29 (.leaf (9)) (.leaf (34))))) (.branch 33 (.branch 31 (.leaf (36)) (.branch 32 (.leaf (37)) (.leaf (39)))) (.branch 34 (.leaf (40)) (.branch 35 (.leaf (35)) (.leaf (16)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (26)) (.branch 38 (.leaf (41)) (.leaf (42)))) (.branch 40 (.leaf (28)) (.branch 41 (.leaf (43)) (.leaf (44))))) (.branch 45 (.branch 43 (.leaf (46)) (.branch 44 (.leaf (47)) (.leaf (45)))) (.branch 46 (.leaf (31)) (.branch 47 (.leaf (38)) (.leaf (33))))))))
noncomputable def T (p : Fin 48) : Fin 48 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (18)) (.branch 2 (.leaf (13)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (22)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (19)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 10 (.leaf (28)) (.branch 11 (.leaf (5)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (21)) (.branch 14 (.leaf (7)) (.leaf (8)))) (.branch 16 (.leaf (9)) (.branch 17 (.leaf (35)) (.leaf (10))))) (.branch 21 (.branch 19 (.leaf (17)) (.branch 20 (.leaf (11)) (.leaf (12)))) (.branch 22 (.leaf (26)) (.branch 23 (.leaf (14)) (.leaf (15))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (16)) (.branch 26 (.leaf (20)) (.leaf (36)))) (.branch 28 (.leaf (23)) (.branch 29 (.leaf (39)) (.leaf (24))))) (.branch 33 (.branch 31 (.leaf (25)) (.branch 32 (.leaf (45)) (.leaf (27)))) (.branch 34 (.leaf (47)) (.branch 35 (.leaf (29)) (.leaf (34)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (30)) (.branch 38 (.leaf (31)) (.leaf (46)))) (.branch 40 (.leaf (32)) (.branch 41 (.leaf (33)) (.leaf (37))))) (.branch 45 (.branch 43 (.leaf (38)) (.branch 44 (.leaf (40)) (.leaf (41)))) (.branch 46 (.leaf (44)) (.branch 47 (.leaf (42)) (.leaf (43))))))))
noncomputable def Ti (p : Fin 48) : Fin 48 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 48) : Fin 48 := T (S p)
theorem quotient_relations : (∀ p : Fin 48, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 96, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 96, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 48, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 48)) := [[0,3,11],[1,2,8],[4,5,15],[6,7,20],[9,10,24],[12,13,14],[16,17,30],[18,19,25],[21,22,23],[26,27,37],[28,29,40],[31,32,42],[33,34,44],[35,36,41],[38,39,43],[45,46,47]]
noncomputable def verticesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (13)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (15)) (.branch 14 (.leaf (16)) (.leaf (17)))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (18)) (.leaf (19))))) (.branch 21 (.branch 19 (.leaf (21)) (.branch 20 (.leaf (22)) (.leaf (11)))) (.branch 22 (.leaf (24)) (.branch 23 (.leaf (25)) (.leaf (26))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (14)) (.branch 26 (.leaf (23)) (.leaf (27)))) (.branch 28 (.leaf (28)) (.branch 29 (.leaf (30)) (.leaf (31))))) (.branch 33 (.branch 31 (.leaf (20)) (.branch 32 (.leaf (33)) (.leaf (34)))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (37)) (.leaf (39)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (40)) (.branch 38 (.leaf (29)) (.leaf (42)))) (.branch 40 (.leaf (43)) (.branch 41 (.leaf (32)) (.leaf (41))))) (.branch 45 (.branch 43 (.leaf (35)) (.branch 44 (.leaf (44)) (.leaf (38)))) (.branch 46 (.leaf (45)) (.branch 47 (.leaf (46)) (.leaf (47))))))))
noncomputable def verticesIndex (p : Fin 48) : Fin 48 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (11)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (15)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (20)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (24)))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (14))))) (.branch 21 (.branch 19 (.leaf (16)) (.branch 20 (.leaf (17)) (.leaf (30)))) (.branch 22 (.leaf (18)) (.branch 23 (.leaf (19)) (.leaf (25))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (21)) (.branch 26 (.leaf (22)) (.leaf (23)))) (.branch 28 (.leaf (26)) (.branch 29 (.leaf (27)) (.leaf (37))))) (.branch 33 (.branch 31 (.leaf (28)) (.branch 32 (.leaf (29)) (.leaf (40)))) (.branch 34 (.leaf (31)) (.branch 35 (.leaf (32)) (.leaf (42)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (33)) (.branch 38 (.leaf (34)) (.leaf (44)))) (.branch 40 (.leaf (35)) (.branch 41 (.leaf (36)) (.leaf (41))))) (.branch 45 (.branch 43 (.leaf (38)) (.branch 44 (.leaf (39)) (.leaf (43)))) (.branch 46 (.leaf (45)) (.branch 47 (.leaf (46)) (.leaf (47))))))))
noncomputable def verticesBack (p : Fin 48) : Fin 48 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 48, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 48 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 48, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 48)) := [[0,1],[2,4],[3,6],[5,9],[7,12],[8,13],[10,16],[11,18],[14,21],[15,22],[17,25],[19,20],[23,26],[24,28],[27,31],[29,33],[30,35],[32,38],[34,41],[36,37],[39,40],[42,45],[43,46],[44,47]]
noncomputable def edgesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (10)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (12)) (.leaf (14)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (11)) (.leaf (16)))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (13)) (.leaf (20))))) (.branch 21 (.branch 19 (.leaf (15)) (.branch 20 (.leaf (22)) (.leaf (23)))) (.branch 22 (.leaf (17)) (.branch 23 (.leaf (19)) (.leaf (24))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (26)) (.branch 26 (.leaf (21)) (.leaf (25)))) (.branch 28 (.leaf (28)) (.branch 29 (.leaf (27)) (.leaf (30))))) (.branch 33 (.branch 31 (.leaf (32)) (.branch 32 (.leaf (29)) (.leaf (34)))) (.branch 34 (.leaf (31)) (.branch 35 (.leaf (36)) (.leaf (33)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (38)) (.branch 38 (.leaf (39)) (.leaf (35)))) (.branch 40 (.leaf (40)) (.branch 41 (.leaf (41)) (.leaf (37))))) (.branch 45 (.branch 43 (.leaf (42)) (.branch 44 (.leaf (44)) (.leaf (46)))) (.branch 46 (.leaf (43)) (.branch 47 (.leaf (45)) (.leaf (47))))))))
noncomputable def edgesIndex (p : Fin 48) : Fin 48 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (8)) (.leaf (13)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (10)) (.branch 14 (.leaf (16)) (.leaf (11)))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (14)) (.leaf (21))))) (.branch 21 (.branch 19 (.leaf (15)) (.branch 20 (.leaf (22)) (.leaf (17)))) (.branch 22 (.leaf (25)) (.branch 23 (.leaf (19)) (.leaf (20))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (23)) (.branch 26 (.leaf (26)) (.leaf (24)))) (.branch 28 (.leaf (28)) (.branch 29 (.leaf (27)) (.leaf (31))))) (.branch 33 (.branch 31 (.leaf (29)) (.branch 32 (.leaf (33)) (.leaf (30)))) (.branch 34 (.leaf (35)) (.branch 35 (.leaf (32)) (.leaf (38)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (34)) (.branch 38 (.leaf (41)) (.leaf (36)))) (.branch 40 (.leaf (37)) (.branch 41 (.leaf (39)) (.leaf (40))))) (.branch 45 (.branch 43 (.leaf (42)) (.branch 44 (.leaf (45)) (.leaf (43)))) (.branch 46 (.leaf (46)) (.branch 47 (.leaf (44)) (.leaf (47))))))))
noncomputable def edgesBack (p : Fin 48) : Fin 48 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 48, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 48 := by decide +kernel
theorem edges_partition : ∀ p : Fin 48, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 48)) := [[0,2,5,10,17,18],[1,3,7,13],[4,8,14,22],[6,11,19],[9,15,23,27,32,39,28],[12,20,25,30,36,26,21],[16,24,29,34,35],[31,37,41,44,45],[33,40,43,47],[38,42,46]]
noncomputable def facesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (6)) (.leaf (1)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (10)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (14)) (.branch 8 (.leaf (8)) (.leaf (11)))) (.branch 10 (.leaf (17)) (.branch 11 (.leaf (3)) (.leaf (15)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (24)) (.branch 14 (.leaf (9)) (.leaf (12)))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (31)) (.leaf (4))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (16)) (.leaf (25)))) (.branch 22 (.leaf (30)) (.branch 23 (.leaf (13)) (.leaf (19))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (32)) (.branch 26 (.leaf (26)) (.leaf (29)))) (.branch 28 (.leaf (20)) (.branch 29 (.leaf (23)) (.leaf (33))))) (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (36)) (.leaf (21)))) (.branch 34 (.leaf (41)) (.branch 35 (.leaf (34)) (.leaf (35)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (28)) (.branch 38 (.leaf (37)) (.leaf (45)))) (.branch 40 (.leaf (22)) (.branch 41 (.leaf (42)) (.leaf (38))))) (.branch 45 (.branch 43 (.leaf (46)) (.branch 44 (.leaf (43)) (.leaf (39)))) (.branch 46 (.leaf (40)) (.branch 47 (.leaf (47)) (.leaf (44))))))))
noncomputable def facesIndex (p : Fin 48) : Fin 48 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (10)) (.branch 5 (.leaf (17)) (.leaf (18))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (7)))) (.branch 10 (.leaf (13)) (.branch 11 (.leaf (4)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (14)) (.branch 14 (.leaf (22)) (.leaf (6)))) (.branch 16 (.leaf (11)) (.branch 17 (.leaf (19)) (.leaf (9))))) (.branch 21 (.branch 19 (.leaf (15)) (.branch 20 (.leaf (23)) (.leaf (27)))) (.branch 22 (.leaf (32)) (.branch 23 (.leaf (39)) (.leaf (28))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (12)) (.branch 26 (.leaf (20)) (.leaf (25)))) (.branch 28 (.leaf (30)) (.branch 29 (.leaf (36)) (.leaf (26))))) (.branch 33 (.branch 31 (.leaf (21)) (.branch 32 (.leaf (16)) (.leaf (24)))) (.branch 34 (.leaf (29)) (.branch 35 (.leaf (34)) (.leaf (35)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (31)) (.branch 38 (.leaf (37)) (.leaf (41)))) (.branch 40 (.leaf (44)) (.branch 41 (.leaf (45)) (.leaf (33))))) (.branch 45 (.branch 43 (.leaf (40)) (.branch 44 (.leaf (43)) (.leaf (47)))) (.branch 46 (.leaf (38)) (.branch 47 (.leaf (42)) (.leaf (46))))))))
noncomputable def facesBack (p : Fin 48) : Fin 48 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 48, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 48 := by decide +kernel
theorem faces_partition : ∀ p : Fin 48, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [6,4,4,3,7,7,5,5,4,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 16 - 24 + 10 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))) (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.branch 11 (.leaf (⟨-1,-3,0,-1⟩)) (.leaf (⟨-1,-1,1,0⟩)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (⟨1,0,2,1⟩)) (.branch 14 (.leaf (⟨0,1,-1,1⟩)) (.leaf (⟨1,1,1,2⟩)))) (.branch 16 (.leaf (⟨2,1,1,1⟩)) (.branch 17 (.leaf (⟨-3,1,-1,0⟩)) (.leaf (⟨1,4,0,1⟩))))) (.branch 21 (.branch 19 (.leaf (⟨-1,-5,0,-1⟩)) (.branch 20 (.leaf (⟨-5,-4,-1,-1⟩)) (.leaf (⟨1,1,-2,-1⟩)))) (.branch 22 (.leaf (⟨-3,-1,-2,-1⟩)) (.branch 23 (.leaf (⟨1,-2,1,-1⟩)) (.leaf (⟨-2,-3,-1,-2⟩))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (⟨-3,-2,-1,-1⟩)) (.branch 26 (.leaf (⟨4,-1,1,0⟩)) (.leaf (⟨-3,2,-2,1⟩)))) (.branch 28 (.leaf (⟨2,5,1,3⟩)) (.branch 29 (.leaf (⟨-2,3,-1,1⟩)) (.leaf (⟨3,5,1,2⟩))))) (.branch 33 (.branch 31 (.leaf (⟨4,3,1,1⟩)) (.branch 32 (.leaf (⟨5,-2,3,-1⟩)) (.leaf (⟨-2,-7,-1,-4⟩)))) (.branch 34 (.leaf (⟨5,-3,2,-1⟩)) (.branch 35 (.leaf (⟨-3,-8,-1,-3⟩)) (.leaf (⟨3,-4,1,-1⟩)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (⟨-4,-7,-1,-2⟩)) (.branch 38 (.leaf (⟨5,3,3,2⟩)) (.leaf (⟨-7,-2,-3,-1⟩)))) (.branch 40 (.leaf (⟨2,-5,1,-2⟩)) (.branch 41 (.leaf (⟨5,2,2,1⟩)) (.leaf (⟨-7,-3,-2,-1⟩))))) (.branch 45 (.branch 43 (.leaf (⟨-7,-5,-4,-3⟩)) (.branch 44 (.leaf (⟨-5,-7,-2,-3⟩)) (.leaf (⟨-8,-5,-3,-2⟩)))) (.branch 46 (.leaf (⟨8,13,3,5⟩)) (.branch 47 (.leaf (⟨13,5,5,2⟩)) (.leaf (⟨-5,8,-2,3⟩))))))))
noncomputable def liftMatrix (p : Fin 48) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 48) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],13⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],14⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],15⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],16⟩,⟨⟨1,4,0,1⟩,[.t (4)],17⟩,⟨⟨-1,-5,0,-1⟩,[.t (5)],18⟩,⟨⟨-5,-4,-1,-1⟩,[.t (5),.s,.t (1)],19⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],20⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],21⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],22⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],23⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],24⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],25⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],26⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],27⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],28⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],29⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],30⟩,⟨⟨5,-2,3,-1⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],31⟩,⟨⟨-2,-7,-1,-4⟩,[.t (2),.s,.t (4)],32⟩,⟨⟨5,-3,2,-1⟩,[.t (2),.s,.t (-2),.s,.t (-1)],33⟩,⟨⟨-3,-8,-1,-3⟩,[.t (3),.s,.t (3)],34⟩,⟨⟨3,-4,1,-1⟩,[.t (3),.s,.t (-1)],35⟩,⟨⟨-4,-7,-1,-2⟩,[.t (4),.s,.t (2)],36⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],37⟩,⟨⟨-7,-2,-3,-1⟩,[.t (2),.s,.t (-3),.s,.t (0)],38⟩,⟨⟨2,-5,1,-2⟩,[.t (2),.s,.t (-2)],39⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],40⟩,⟨⟨-7,-3,-2,-1⟩,[.t (3),.s,.t (-2),.s,.t (0)],41⟩,⟨⟨-7,-5,-4,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],42⟩,⟨⟨-5,-7,-2,-3⟩,[.t (2),.s,.t (-2),.s,.t (1)],43⟩,⟨⟨-8,-5,-3,-2⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (0)],44⟩,⟨⟨8,13,3,5⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (1)],45⟩,⟨⟨13,5,5,2⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (0)],46⟩,⟨⟨-5,8,-2,3⟩,[.t (2),.s,.t (-2),.s,.t (-2)],47⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 48 ∧ ((List.finRange 48).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 48) := [⟨11,2,⟨⟨-1,-6,0,-1⟩,[.t (6)],0⟩⟩,⟨20,4,⟨⟨-14,-9,-3,-2⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,1,⟨⟨-1,0,-4,-1⟩,[.t (0),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨12,1,⟨⟨-1,0,4,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨14,3,⟨⟨-5,4,-4,3⟩,[.t (1),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨21,3,⟨⟨3,-4,4,-5⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨37,7,⟨⟨26,-41,7,-11⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨42,8,⟨⟨-71,121,-27,46⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2)],0⟩⟩,⟨32,5,⟨⟨15,-28,7,-13⟩,[.t (2),.s,.t (-7),.s,.t (-2)],0⟩⟩,⟨38,5,⟨⟨-13,28,-7,15⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨43,9,⟨⟨-41,100,-16,39⟩,[.t (2),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨46,9,⟨⟨39,-100,16,-41⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨45,8,⟨⟨46,-121,27,-71⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨34,6,⟨⟨16,-45,5,-14⟩,[.t (3),.s,.t (-5),.s,.t (-3)],0⟩⟩,⟨41,6,⟨⟨-14,45,-5,16⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨36,7,⟨⟨-11,41,-7,26⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-4)],0⟩⟩,⟨19,4,⟨⟨-2,9,3,-14⟩,[.t (-1),.s,.t (-3),.s,.t (-5)],0⟩⟩,⟨18,2,⟨⟨-1,6,0,-1⟩,[.t (-6)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-1,2),(0,1),(1,2),(1,1),(3,2),(5,3),(7,4),(2,1),(7,3),(5,2),(13,5),(8,3),(3,1),(7,2),(4,1),(5,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end A7_c14

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
