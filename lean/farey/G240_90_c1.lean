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
namespace G240_90_c1
noncomputable def originalSData : LookupTree (Fin 96) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (9)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (12)) (.branch 8 (.leaf (0)) (.leaf (15)))) (.branch 10 (.leaf (14)) (.branch 11 (.leaf (18)) (.leaf (20)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (16)) (.branch 14 (.leaf (22)) (.leaf (24)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (19)) (.leaf (28))))) (.branch 21 (.branch 19 (.leaf (25)) (.branch 20 (.leaf (6)) (.leaf (26)))) (.branch 22 (.leaf (11)) (.branch 23 (.leaf (27)) (.leaf (31))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (4)) (.branch 26 (.leaf (34)) (.leaf (21)))) (.branch 28 (.leaf (35)) (.branch 29 (.leaf (33)) (.leaf (37))))) (.branch 33 (.branch 31 (.leaf (39)) (.branch 32 (.leaf (36)) (.leaf (17)))) (.branch 34 (.leaf (32)) (.branch 35 (.leaf (10)) (.leaf (13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (44)) (.branch 38 (.leaf (42)) (.leaf (45)))) (.branch 40 (.leaf (43)) (.branch 41 (.leaf (47)) (.leaf (49))))) (.branch 45 (.branch 43 (.leaf (50)) (.branch 44 (.leaf (52)) (.leaf (23)))) (.branch 46 (.leaf (51)) (.branch 47 (.leaf (55)) (.leaf (53)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (58)) (.branch 50 (.leaf (54)) (.leaf (29)))) (.branch 52 (.leaf (60)) (.branch 53 (.leaf (30)) (.leaf (62))))) (.branch 57 (.branch 55 (.leaf (64)) (.branch 56 (.leaf (61)) (.leaf (66)))) (.branch 58 (.leaf (67)) (.branch 59 (.leaf (63)) (.leaf (70)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (38)) (.branch 62 (.leaf (71)) (.leaf (40)))) (.branch 64 (.leaf (74)) (.branch 65 (.leaf (41)) (.leaf (59))))) (.branch 69 (.branch 67 (.leaf (72)) (.branch 68 (.leaf (73)) (.leaf (78)))) (.branch 70 (.leaf (68)) (.branch 71 (.leaf (75)) (.leaf (46))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (80)) (.branch 74 (.leaf (81)) (.leaf (48)))) (.branch 76 (.leaf (65)) (.branch 77 (.leaf (83)) (.leaf (85))))) (.branch 81 (.branch 79 (.leaf (82)) (.branch 80 (.leaf (87)) (.leaf (56)))) (.branch 82 (.leaf (57)) (.branch 83 (.leaf (69)) (.leaf (79)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (90)) (.branch 86 (.leaf (89)) (.leaf (92)))) (.branch 88 (.leaf (76)) (.branch 89 (.leaf (93)) (.leaf (91))))) (.branch 93 (.branch 91 (.leaf (88)) (.branch 92 (.leaf (77)) (.leaf (94)))) (.branch 94 (.leaf (84)) (.branch 95 (.leaf (95)) (.leaf (86)))))))))
noncomputable def originalS (p : Fin 96) : Fin 96 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 96) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (10)) (.leaf (11))))) (.branch 9 (.branch 7 (.leaf (13)) (.branch 8 (.leaf (14)) (.leaf (16)))) (.branch 10 (.leaf (17)) (.branch 11 (.leaf (19)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (21)) (.branch 14 (.leaf (23)) (.leaf (25)))) (.branch 16 (.leaf (26)) (.branch 17 (.leaf (27)) (.leaf (29))))) (.branch 21 (.branch 19 (.leaf (30)) (.branch 20 (.leaf (20)) (.leaf (1)))) (.branch 22 (.leaf (7)) (.branch 23 (.leaf (18)) (.leaf (32))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (33)) (.branch 26 (.leaf (12)) (.leaf (15)))) (.branch 28 (.leaf (36)) (.branch 29 (.leaf (3)) (.leaf (38))))) (.branch 33 (.branch 31 (.leaf (40)) (.branch 32 (.leaf (41)) (.leaf (0)))) (.branch 34 (.leaf (42)) (.branch 35 (.leaf (43)) (.leaf (34)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (28)) (.branch 38 (.leaf (31)) (.leaf (46)))) (.branch 40 (.leaf (9)) (.branch 41 (.leaf (48)) (.leaf (50))))) (.branch 45 (.branch 43 (.leaf (51)) (.branch 44 (.leaf (53)) (.leaf (54)))) (.branch 46 (.leaf (49)) (.branch 47 (.leaf (56)) (.leaf (57)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (59)) (.branch 50 (.leaf (22)) (.leaf (44)))) (.branch 52 (.leaf (61)) (.branch 53 (.leaf (24)) (.leaf (63))))) (.branch 57 (.branch 55 (.leaf (37)) (.branch 56 (.leaf (65)) (.leaf (67)))) (.branch 58 (.leaf (68)) (.branch 59 (.leaf (69)) (.leaf (45)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (64)) (.branch 62 (.leaf (72)) (.leaf (73)))) (.branch 64 (.leaf (75)) (.branch 65 (.leaf (35)) (.leaf (76))))) (.branch 69 (.branch 67 (.leaf (77)) (.branch 68 (.leaf (39)) (.leaf (47)))) (.branch 70 (.leaf (66)) (.branch 71 (.leaf (79)) (.leaf (70))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (81)) (.branch 74 (.leaf (82)) (.leaf (78)))) (.branch 76 (.leaf (60)) (.branch 77 (.leaf (84)) (.leaf (86))))) (.branch 81 (.branch 79 (.leaf (80)) (.branch 80 (.leaf (88)) (.leaf (89)))) (.branch 82 (.leaf (52)) (.branch 83 (.leaf (62)) (.leaf (74)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (91)) (.branch 86 (.leaf (55)) (.leaf (87)))) (.branch 88 (.leaf (58)) (.branch 89 (.leaf (85)) (.leaf (94))))) (.branch 93 (.branch 91 (.leaf (92)) (.branch 92 (.leaf (71)) (.leaf (90)))) (.branch 94 (.leaf (95)) (.branch 95 (.leaf (83)) (.leaf (93)))))))))
noncomputable def originalT (p : Fin 96) : Fin 96 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 48) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (3)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (5)) (.leaf (11))))) (.branch 21 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (9)) (.leaf (13)))) (.branch 22 (.leaf (13)) (.branch 23 (.leaf (14)) (.leaf (15))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (6)) (.branch 26 (.leaf (7)) (.leaf (8)))) (.branch 28 (.leaf (10)) (.branch 29 (.leaf (16)) (.leaf (17))))) (.branch 33 (.branch 31 (.leaf (18)) (.branch 32 (.leaf (19)) (.leaf (16)))) (.branch 34 (.leaf (11)) (.branch 35 (.leaf (12)) (.leaf (14)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (15)) (.branch 38 (.leaf (20)) (.leaf (21)))) (.branch 40 (.leaf (22)) (.branch 41 (.leaf (23)) (.leaf (24))))) (.branch 45 (.branch 43 (.leaf (17)) (.branch 44 (.leaf (18)) (.leaf (19)))) (.branch 46 (.leaf (25)) (.branch 47 (.leaf (26)) (.leaf (27)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (28)) (.branch 50 (.leaf (29)) (.leaf (20)))) (.branch 52 (.leaf (21)) (.branch 53 (.leaf (22)) (.leaf (23))))) (.branch 57 (.branch 55 (.leaf (24)) (.branch 56 (.leaf (30)) (.leaf (31)))) (.branch 58 (.leaf (32)) (.branch 59 (.leaf (33)) (.leaf (34)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (25)) (.branch 62 (.leaf (26)) (.leaf (27)))) (.branch 64 (.leaf (28)) (.branch 65 (.leaf (29)) (.leaf (35))))) (.branch 69 (.branch 67 (.leaf (36)) (.branch 68 (.leaf (37)) (.leaf (38)))) (.branch 70 (.leaf (39)) (.branch 71 (.leaf (35)) (.leaf (30))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (31)) (.branch 74 (.leaf (32)) (.leaf (33)))) (.branch 76 (.leaf (34)) (.branch 77 (.leaf (40)) (.leaf (41))))) (.branch 81 (.branch 79 (.leaf (39)) (.branch 80 (.leaf (40)) (.leaf (36)))) (.branch 82 (.leaf (37)) (.branch 83 (.leaf (38)) (.leaf (42)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (43)) (.branch 86 (.leaf (44)) (.leaf (45)))) (.branch 88 (.leaf (42)) (.branch 89 (.leaf (43)) (.leaf (41))))) (.branch 93 (.branch 91 (.leaf (46)) (.branch 92 (.leaf (44)) (.leaf (47)))) (.branch 94 (.leaf (46)) (.branch 95 (.leaf (45)) (.leaf (47)))))))))
noncomputable def projection (p : Fin 96) : Fin 48 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 96) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (11)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (13)) (.leaf (17)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (18)) (.branch 14 (.leaf (20)) (.leaf (22)))) (.branch 16 (.leaf (23)) (.branch 17 (.leaf (28)) (.leaf (29))))) (.branch 21 (.branch 19 (.leaf (30)) (.branch 20 (.leaf (31)) (.leaf (37)))) (.branch 22 (.leaf (38)) (.branch 23 (.leaf (39)) (.leaf (40))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (41)) (.branch 26 (.leaf (45)) (.leaf (46)))) (.branch 28 (.leaf (47)) (.branch 29 (.leaf (48)) (.leaf (49))))) (.branch 33 (.branch 31 (.leaf (55)) (.branch 32 (.leaf (56)) (.leaf (57)))) (.branch 34 (.leaf (58)) (.branch 35 (.leaf (59)) (.leaf (65)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (66)) (.branch 38 (.leaf (67)) (.leaf (68)))) (.branch 40 (.leaf (69)) (.branch 41 (.leaf (76)) (.leaf (77))))) (.branch 45 (.branch 43 (.leaf (83)) (.branch 44 (.leaf (84)) (.leaf (85)))) (.branch 46 (.leaf (86)) (.branch 47 (.leaf (90)) (.leaf (92))))))))
noncomputable def representative (p : Fin 48) : Fin 96 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (13)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (14)) (.leaf (16)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (10)))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (11)) (.leaf (20))))) (.branch 21 (.branch 19 (.leaf (22)) (.branch 20 (.leaf (15)) (.leaf (17)))) (.branch 22 (.leaf (25)) (.branch 23 (.leaf (18)) (.leaf (27))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (29)) (.branch 26 (.leaf (21)) (.leaf (30)))) (.branch 28 (.leaf (23)) (.branch 29 (.leaf (33)) (.leaf (24))))) (.branch 33 (.branch 31 (.leaf (26)) (.branch 32 (.leaf (36)) (.leaf (37)))) (.branch 34 (.leaf (28)) (.branch 35 (.leaf (35)) (.leaf (34)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (31)) (.branch 38 (.leaf (32)) (.leaf (39)))) (.branch 40 (.leaf (38)) (.branch 41 (.leaf (42)) (.leaf (44))))) (.branch 45 (.branch 43 (.leaf (40)) (.branch 44 (.leaf (46)) (.leaf (41)))) (.branch 46 (.leaf (47)) (.branch 47 (.leaf (43)) (.leaf (45))))))))
noncomputable def S (p : Fin 48) : Fin 48 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (8)) (.leaf (10))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (9)) (.leaf (4)))) (.branch 10 (.leaf (13)) (.branch 11 (.leaf (15)) (.leaf (17)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (18)) (.branch 14 (.leaf (1)) (.leaf (12)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (0)) (.leaf (21))))) (.branch 21 (.branch 19 (.leaf (23)) (.branch 20 (.leaf (24)) (.leaf (19)))) (.branch 22 (.leaf (26)) (.branch 23 (.leaf (6)) (.leaf (28))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (20)) (.branch 26 (.leaf (29)) (.leaf (31)))) (.branch 28 (.leaf (32)) (.branch 29 (.leaf (34)) (.leaf (14))))) (.branch 33 (.branch 31 (.leaf (35)) (.branch 32 (.leaf (37)) (.leaf (38)))) (.branch 34 (.leaf (39)) (.branch 35 (.leaf (25)) (.leaf (40)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (41)) (.branch 38 (.leaf (22)) (.leaf (27)))) (.branch 40 (.leaf (36)) (.branch 41 (.leaf (43)) (.leaf (45))))) (.branch 45 (.branch 43 (.leaf (33)) (.branch 44 (.leaf (44)) (.leaf (30)))) (.branch 46 (.leaf (42)) (.branch 47 (.leaf (47)) (.leaf (46))))))))
noncomputable def T (p : Fin 48) : Fin 48 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (16)) (.branch 2 (.leaf (13)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (8)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (22)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (5)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (14)) (.branch 14 (.leaf (9)) (.leaf (29)))) (.branch 16 (.leaf (10)) (.branch 17 (.leaf (15)) (.leaf (11))))) (.branch 21 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (20)) (.leaf (24)))) (.branch 22 (.leaf (17)) (.branch 23 (.leaf (37)) (.leaf (18))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (19)) (.branch 26 (.leaf (34)) (.leaf (21)))) (.branch 28 (.leaf (38)) (.branch 29 (.leaf (23)) (.leaf (25))))) (.branch 33 (.branch 31 (.leaf (44)) (.branch 32 (.leaf (26)) (.leaf (27)))) (.branch 34 (.leaf (42)) (.branch 35 (.leaf (28)) (.leaf (30)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (39)) (.branch 38 (.leaf (31)) (.leaf (32)))) (.branch 40 (.leaf (33)) (.branch 41 (.leaf (35)) (.leaf (36))))) (.branch 45 (.branch 43 (.leaf (45)) (.branch 44 (.leaf (40)) (.leaf (43)))) (.branch 46 (.leaf (41)) (.branch 47 (.leaf (47)) (.leaf (46))))))))
noncomputable def Ti (p : Fin 48) : Fin 48 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 48) : Fin 48 := T (S p)
theorem quotient_relations : (∀ p : Fin 48, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 96, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 96, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 48, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 48)) := [[0,3,11],[1,2,8],[4,5,13],[6,7,18],[9,10,12],[14,15,24],[16,17,19],[20,21,29],[22,23,32],[25,26,35],[27,28,39],[30,31,41],[33,34,40],[36,37,38],[42,43,47],[44,45,46]]
noncomputable def verticesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (13)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (14)) (.branch 14 (.leaf (8)) (.leaf (15)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (18)) (.leaf (19))))) (.branch 21 (.branch 19 (.leaf (11)) (.branch 20 (.leaf (20)) (.leaf (21)))) (.branch 22 (.leaf (22)) (.branch 23 (.leaf (24)) (.leaf (25))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (17)) (.branch 26 (.leaf (27)) (.leaf (28)))) (.branch 28 (.leaf (30)) (.branch 29 (.leaf (31)) (.leaf (23))))) (.branch 33 (.branch 31 (.leaf (33)) (.branch 32 (.leaf (34)) (.leaf (26)))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (37)) (.leaf (29)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (39)) (.branch 38 (.leaf (40)) (.leaf (41)))) (.branch 40 (.leaf (32)) (.branch 41 (.leaf (38)) (.leaf (35))))) (.branch 45 (.branch 43 (.leaf (42)) (.branch 44 (.leaf (43)) (.leaf (45)))) (.branch 46 (.leaf (46)) (.branch 47 (.leaf (47)) (.leaf (44))))))))
noncomputable def verticesIndex (p : Fin 48) : Fin 48 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (11)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (13)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (18)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (12)))) (.branch 16 (.leaf (14)) (.branch 17 (.leaf (15)) (.leaf (24))))) (.branch 21 (.branch 19 (.leaf (16)) (.branch 20 (.leaf (17)) (.leaf (19)))) (.branch 22 (.leaf (20)) (.branch 23 (.leaf (21)) (.leaf (29))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (22)) (.branch 26 (.leaf (23)) (.leaf (32)))) (.branch 28 (.leaf (25)) (.branch 29 (.leaf (26)) (.leaf (35))))) (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (28)) (.leaf (39)))) (.branch 34 (.leaf (30)) (.branch 35 (.leaf (31)) (.leaf (41)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (33)) (.branch 38 (.leaf (34)) (.leaf (40)))) (.branch 40 (.leaf (36)) (.branch 41 (.leaf (37)) (.leaf (38))))) (.branch 45 (.branch 43 (.leaf (42)) (.branch 44 (.leaf (43)) (.leaf (47)))) (.branch 46 (.leaf (44)) (.branch 47 (.leaf (45)) (.leaf (46))))))))
noncomputable def verticesBack (p : Fin 48) : Fin 48 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 48, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 48 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 48, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 48)) := [[0,1],[2,4],[3,6],[5,9],[7,12],[8,13],[10,14],[11,16],[15,19],[17,20],[18,22],[21,25],[23,27],[24,29],[26,30],[28,33],[31,36],[32,37],[34,35],[38,39],[40,42],[41,44],[43,46],[45,47]]
noncomputable def edgesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (10)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (12)) (.leaf (14)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (11)) (.leaf (13)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (15)) (.leaf (18))))) (.branch 21 (.branch 19 (.leaf (20)) (.branch 20 (.leaf (17)) (.leaf (19)))) (.branch 22 (.leaf (22)) (.branch 23 (.leaf (21)) (.leaf (24))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (26)) (.branch 26 (.leaf (23)) (.leaf (28)))) (.branch 28 (.leaf (25)) (.branch 29 (.leaf (30)) (.leaf (27))))) (.branch 33 (.branch 31 (.leaf (29)) (.branch 32 (.leaf (32)) (.leaf (34)))) (.branch 34 (.leaf (31)) (.branch 35 (.leaf (36)) (.leaf (37)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (33)) (.branch 38 (.leaf (35)) (.leaf (38)))) (.branch 40 (.leaf (39)) (.branch 41 (.leaf (40)) (.leaf (42))))) (.branch 45 (.branch 43 (.leaf (41)) (.branch 44 (.leaf (44)) (.leaf (43)))) (.branch 46 (.leaf (46)) (.branch 47 (.leaf (45)) (.leaf (47))))))))
noncomputable def edgesIndex (p : Fin 48) : Fin 48 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (8)) (.leaf (13)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (10)) (.branch 14 (.leaf (14)) (.leaf (11)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (15)) (.leaf (19))))) (.branch 21 (.branch 19 (.leaf (17)) (.branch 20 (.leaf (20)) (.leaf (18)))) (.branch 22 (.leaf (22)) (.branch 23 (.leaf (21)) (.leaf (25))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (23)) (.branch 26 (.leaf (27)) (.leaf (24)))) (.branch 28 (.leaf (29)) (.branch 29 (.leaf (26)) (.leaf (30))))) (.branch 33 (.branch 31 (.leaf (28)) (.branch 32 (.leaf (33)) (.leaf (31)))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (32)) (.leaf (37)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (34)) (.branch 38 (.leaf (35)) (.leaf (38)))) (.branch 40 (.leaf (39)) (.branch 41 (.leaf (40)) (.leaf (42))))) (.branch 45 (.branch 43 (.leaf (41)) (.branch 44 (.leaf (44)) (.leaf (43)))) (.branch 46 (.leaf (46)) (.branch 47 (.leaf (45)) (.leaf (47))))))))
noncomputable def edgesBack (p : Fin 48) : Fin 48 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 48, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 48 := by decide +kernel
theorem edges_partition : ∀ p : Fin 48, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 48)) := [[0,2,5,10,15,16],[1,3,7,9,13],[4,8],[6,11,17,21,26,31,37,22],[12,18,23,28,34,25,29,14],[19,24,20],[27,32,38],[30,35,40,43,44],[33,39,36,41,45,42],[46,47]]
noncomputable def facesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (6)) (.leaf (1)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (11)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (13)) (.branch 8 (.leaf (8)) (.leaf (12)))) (.branch 10 (.leaf (9)) (.branch 11 (.leaf (3)) (.leaf (14)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (21)) (.branch 14 (.leaf (10)) (.leaf (28)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (5)) (.leaf (15))))) (.branch 21 (.branch 19 (.leaf (22)) (.branch 20 (.leaf (29)) (.leaf (31)))) (.branch 22 (.leaf (16)) (.branch 23 (.leaf (20)) (.leaf (23))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (30)) (.branch 26 (.leaf (26)) (.leaf (17)))) (.branch 28 (.leaf (32)) (.branch 29 (.leaf (24)) (.leaf (27))))) (.branch 33 (.branch 31 (.leaf (35)) (.branch 32 (.leaf (18)) (.leaf (33)))) (.branch 34 (.leaf (40)) (.branch 35 (.leaf (25)) (.leaf (36)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (42)) (.branch 38 (.leaf (19)) (.leaf (34)))) (.branch 40 (.leaf (41)) (.branch 41 (.leaf (37)) (.leaf (43))))) (.branch 45 (.branch 43 (.leaf (45)) (.branch 44 (.leaf (38)) (.leaf (39)))) (.branch 46 (.leaf (44)) (.branch 47 (.leaf (46)) (.leaf (47))))))))
noncomputable def facesIndex (p : Fin 48) : Fin 48 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (10)) (.branch 5 (.leaf (15)) (.leaf (16))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (7)))) (.branch 10 (.leaf (9)) (.branch 11 (.leaf (13)) (.leaf (4)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (8)) (.branch 14 (.leaf (6)) (.leaf (11)))) (.branch 16 (.leaf (17)) (.branch 17 (.leaf (21)) (.leaf (26))))) (.branch 21 (.branch 19 (.leaf (31)) (.branch 20 (.leaf (37)) (.leaf (22)))) (.branch 22 (.leaf (12)) (.branch 23 (.leaf (18)) (.leaf (23))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (28)) (.branch 26 (.leaf (34)) (.leaf (25)))) (.branch 28 (.leaf (29)) (.branch 29 (.leaf (14)) (.leaf (19))))) (.branch 33 (.branch 31 (.leaf (24)) (.branch 32 (.leaf (20)) (.leaf (27)))) (.branch 34 (.leaf (32)) (.branch 35 (.leaf (38)) (.leaf (30)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (35)) (.branch 38 (.leaf (40)) (.leaf (43)))) (.branch 40 (.leaf (44)) (.branch 41 (.leaf (33)) (.leaf (39))))) (.branch 45 (.branch 43 (.leaf (36)) (.branch 44 (.leaf (41)) (.leaf (45)))) (.branch 46 (.leaf (42)) (.branch 47 (.leaf (46)) (.leaf (47))))))))
noncomputable def facesBack (p : Fin 48) : Fin 48 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 48, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 48 := by decide +kernel
theorem faces_partition : ∀ p : Fin 48, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [6,5,2,8,8,3,3,5,6,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 16 - 24 + 10 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))) (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.branch 11 (.leaf (⟨-1,-3,0,-1⟩)) (.leaf (⟨-1,-1,1,0⟩)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (⟨-3,-2,-1,-1⟩)) (.branch 14 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨-3,1,-1,0⟩)))) (.branch 16 (.leaf (⟨1,4,0,1⟩)) (.branch 17 (.leaf (⟨-1,-5,0,-1⟩)) (.leaf (⟨-5,-4,-1,-1⟩))))) (.branch 21 (.branch 19 (.leaf (⟨1,1,-2,-1⟩)) (.branch 20 (.leaf (⟨4,-1,1,0⟩)) (.leaf (⟨-4,-7,-1,-2⟩)))) (.branch 22 (.leaf (⟨-7,-3,-2,-1⟩)) (.branch 23 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-2,2,3⟩))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (⟨4,3,1,1⟩)) (.branch 26 (.leaf (⟨-3,7,-1,2⟩)) (.leaf (⟨7,10,2,3⟩)))) (.branch 28 (.leaf (⟨-2,1,3,-2⟩)) (.branch 29 (.leaf (⟨1,3,-2,-5⟩)) (.leaf (⟨3,-4,1,-1⟩))))) (.branch 33 (.branch 31 (.leaf (⟨10,-7,3,-2⟩)) (.branch 32 (.leaf (⟨-7,-17,-2,-5⟩)) (.leaf (⟨-2,-1,3,1⟩)))) (.branch 34 (.leaf (⟨-13,-3,-4,-1⟩)) (.branch 35 (.leaf (⟨3,-10,1,-3⟩)) (.leaf (⟨10,3,3,1⟩)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (⟨3,1,-4,-1⟩)) (.branch 38 (.leaf (⟨-1,2,1,-3⟩)) (.leaf (⟨2,3,-3,-4⟩)))) (.branch 40 (.leaf (⟨3,2,-5,-3⟩)) (.branch 41 (.leaf (⟨-10,-13,-3,-4⟩)) (.leaf (⟨-17,-10,-5,-3⟩))))) (.branch 45 (.branch 43 (.leaf (⟨-13,10,-4,3⟩)) (.branch 44 (.leaf (⟨10,23,3,7⟩)) (.leaf (⟨-10,17,-3,5⟩)))) (.branch 46 (.leaf (⟨17,27,5,8⟩)) (.branch 47 (.leaf (⟨27,10,8,3⟩)) (.leaf (⟨23,13,7,4⟩))))))))
noncomputable def liftMatrix (p : Fin 48) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 48) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],12⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],13⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],14⟩,⟨⟨1,4,0,1⟩,[.t (4)],15⟩,⟨⟨-1,-5,0,-1⟩,[.t (5)],16⟩,⟨⟨-5,-4,-1,-1⟩,[.t (5),.s,.t (1)],17⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],18⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],19⟩,⟨⟨-4,-7,-1,-2⟩,[.t (4),.s,.t (2)],20⟩,⟨⟨-7,-3,-2,-1⟩,[.t (3),.s,.t (-2),.s,.t (0)],21⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],22⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],23⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],24⟩,⟨⟨-3,7,-1,2⟩,[.t (3),.s,.t (-2)],25⟩,⟨⟨7,10,2,3⟩,[.t (3),.s,.t (-2),.s,.t (1)],26⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],27⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],28⟩,⟨⟨3,-4,1,-1⟩,[.t (3),.s,.t (-1)],29⟩,⟨⟨10,-7,3,-2⟩,[.t (3),.s,.t (-3),.s,.t (-1)],30⟩,⟨⟨-7,-17,-2,-5⟩,[.t (3),.s,.t (-2),.s,.t (2)],31⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],32⟩,⟨⟨-13,-3,-4,-1⟩,[.t (3),.s,.t (-4),.s,.t (0)],33⟩,⟨⟨3,-10,1,-3⟩,[.t (3),.s,.t (-3)],34⟩,⟨⟨10,3,3,1⟩,[.t (3),.s,.t (-3),.s,.t (0)],35⟩,⟨⟨3,1,-4,-1⟩,[.t (-1),.s,.t (-4),.s,.t (0)],36⟩,⟨⟨-1,2,1,-3⟩,[.t (-1),.s,.t (-3)],37⟩,⟨⟨2,3,-3,-4⟩,[.t (-1),.s,.t (-3),.s,.t (1)],38⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],39⟩,⟨⟨-10,-13,-3,-4⟩,[.t (3),.s,.t (-3),.s,.t (1)],40⟩,⟨⟨-17,-10,-5,-3⟩,[.t (3),.s,.t (-3),.s,.t (-2),.s,.t (0)],41⟩,⟨⟨-13,10,-4,3⟩,[.t (3),.s,.t (-4),.s,.t (-1)],42⟩,⟨⟨10,23,3,7⟩,[.t (3),.s,.t (-3),.s,.t (2)],43⟩,⟨⟨-10,17,-3,5⟩,[.t (3),.s,.t (-3),.s,.t (-2)],44⟩,⟨⟨17,27,5,8⟩,[.t (3),.s,.t (-3),.s,.t (-2),.s,.t (1)],45⟩,⟨⟨27,10,8,3⟩,[.t (3),.s,.t (-3),.s,.t (-3),.s,.t (0)],46⟩,⟨⟨23,13,7,4⟩,[.t (3),.s,.t (-4),.s,.t (-2),.s,.t (0)],47⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 48 ∧ ((List.finRange 48).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 48) := [⟨11,3,⟨⟨-1,-6,0,-1⟩,[.t (6)],0⟩⟩,⟨36,6,⟨⟨-45,-38,-13,-11⟩,[.t (3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨38,7,⟨⟨-17,-12,27,19⟩,[.t (-1),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨39,7,⟨⟨19,12,-27,-17⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨28,5,⟨⟨41,22,13,7⟩,[.t (3),.s,.t (-7),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,1,⟨⟨7,2,3,1⟩,[.t (2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨8,2,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨13,2,⟨⟨1,-2,2,-3⟩,[.t (0),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨12,1,⟨⟨1,-2,-3,7⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨33,5,⟨⟨7,-22,-13,41⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨47,9,⟨⟨-227,742,-67,219⟩,[.t (3),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨43,8,⟨⟨151,-500,45,-149⟩,[.t (3),.s,.t (-3),.s,.t (-6),.s,.t (-2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨46,8,⟨⟨-149,500,-45,151⟩,[.t (3),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨45,9,⟨⟨219,-742,67,-227⟩,[.t (3),.s,.t (-4),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨31,6,⟨⟨-11,38,13,-45⟩,[.t (-1),.s,.t (-7),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨20,4,⟨⟨-13,48,-3,11⟩,[.t (4),.s,.t (-3),.s,.t (-4)],0⟩⟩,⟨17,4,⟨⟨11,-48,3,-13⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨16,3,⟨⟨-1,6,0,-1⟩,[.t (-6)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-3,4),(-2,3),(-3,5),(-1,2),(0,1),(1,1),(2,1),(3,1),(13,4),(23,7),(10,3),(27,8),(17,5),(7,2),(4,1),(5,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G240_90_c1

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
