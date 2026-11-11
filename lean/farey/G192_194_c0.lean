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
namespace G192_194_c0
noncomputable def originalSData : LookupTree (Fin 96) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (9)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (0)) (.leaf (13)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (4)) (.leaf (14)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (10)) (.branch 14 (.leaf (2)) (.leaf (15)))) (.branch 16 (.leaf (6)) (.branch 17 (.leaf (18)) (.leaf (20))))) (.branch 21 (.branch 19 (.leaf (17)) (.branch 20 (.leaf (22)) (.leaf (16)))) (.branch 22 (.leaf (24)) (.branch 23 (.leaf (21)) (.leaf (27))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (19)) (.branch 26 (.leaf (30)) (.leaf (32)))) (.branch 28 (.leaf (25)) (.branch 29 (.leaf (35)) (.leaf (37))))) (.branch 33 (.branch 31 (.leaf (23)) (.branch 32 (.leaf (40)) (.leaf (29)))) (.branch 34 (.leaf (42)) (.branch 35 (.leaf (43)) (.leaf (31)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (46)) (.branch 38 (.leaf (26)) (.leaf (48)))) (.branch 40 (.leaf (49)) (.branch 41 (.leaf (28)) (.leaf (52))))) (.branch 45 (.branch 43 (.leaf (38)) (.branch 44 (.leaf (39)) (.leaf (55)))) (.branch 46 (.leaf (57)) (.branch 47 (.leaf (41)) (.leaf (60)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (33)) (.branch 50 (.leaf (34)) (.leaf (63)))) (.branch 52 (.leaf (65)) (.branch 53 (.leaf (36)) (.leaf (68))))) (.branch 57 (.branch 55 (.leaf (69)) (.branch 56 (.leaf (50)) (.leaf (71)))) (.branch 58 (.leaf (51)) (.branch 59 (.leaf (73)) (.leaf (75)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (53)) (.branch 62 (.leaf (54)) (.leaf (61)))) (.branch 64 (.leaf (44)) (.branch 65 (.leaf (78)) (.leaf (45))))) (.branch 69 (.branch 67 (.leaf (80)) (.branch 68 (.leaf (76)) (.leaf (47)))) (.branch 70 (.leaf (62)) (.branch 71 (.leaf (81)) (.leaf (64))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (84)) (.branch 74 (.leaf (66)) (.leaf (70)))) (.branch 76 (.leaf (67)) (.branch 77 (.leaf (59)) (.leaf (74))))) (.branch 81 (.branch 79 (.leaf (56)) (.branch 80 (.leaf (89)) (.leaf (58)))) (.branch 82 (.leaf (77)) (.branch 83 (.leaf (86)) (.leaf (85)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (79)) (.branch 86 (.leaf (88)) (.leaf (87)))) (.branch 88 (.leaf (91)) (.branch 89 (.leaf (90)) (.leaf (72))))) (.branch 93 (.branch 91 (.leaf (83)) (.branch 92 (.leaf (82)) (.leaf (95)))) (.branch 94 (.leaf (92)) (.branch 95 (.leaf (93)) (.leaf (94)))))))))
noncomputable def originalS (p : Fin 96) : Fin 96 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 96) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (1)) (.leaf (10))))) (.branch 9 (.branch 7 (.leaf (0)) (.branch 8 (.leaf (12)) (.leaf (14)))) (.branch 10 (.leaf (11)) (.branch 11 (.leaf (15)) (.leaf (16)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (9)) (.leaf (3)))) (.branch 16 (.leaf (17)) (.branch 17 (.leaf (19)) (.leaf (21))))) (.branch 21 (.branch 19 (.leaf (5)) (.branch 20 (.leaf (23)) (.leaf (13)))) (.branch 22 (.leaf (25)) (.branch 23 (.leaf (26)) (.leaf (28))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (29)) (.branch 26 (.leaf (31)) (.leaf (33)))) (.branch 28 (.leaf (34)) (.branch 29 (.leaf (36)) (.leaf (38))))) (.branch 33 (.branch 31 (.leaf (39)) (.branch 32 (.leaf (41)) (.leaf (18)))) (.branch 34 (.leaf (43)) (.branch 35 (.leaf (44)) (.leaf (45)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (47)) (.branch 38 (.leaf (20)) (.leaf (49)))) (.branch 40 (.leaf (50)) (.branch 41 (.leaf (51)) (.leaf (53))))) (.branch 45 (.branch 43 (.leaf (54)) (.branch 44 (.leaf (22)) (.leaf (56)))) (.branch 46 (.leaf (58)) (.branch 47 (.leaf (59)) (.leaf (61)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (62)) (.branch 50 (.leaf (24)) (.leaf (64)))) (.branch 52 (.leaf (66)) (.branch 53 (.leaf (67)) (.leaf (69))))) (.branch 57 (.branch 55 (.leaf (70)) (.branch 56 (.leaf (48)) (.leaf (72)))) (.branch 58 (.leaf (27)) (.branch 59 (.leaf (74)) (.leaf (46)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (76)) (.branch 62 (.leaf (37)) (.leaf (77)))) (.branch 64 (.leaf (42)) (.branch 65 (.leaf (79)) (.leaf (30))))) (.branch 69 (.branch 67 (.leaf (81)) (.branch 68 (.leaf (52)) (.leaf (75)))) (.branch 70 (.leaf (32)) (.branch 71 (.leaf (82)) (.leaf (83))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (85)) (.branch 74 (.leaf (86)) (.leaf (68)))) (.branch 76 (.leaf (35)) (.branch 77 (.leaf (40)) (.leaf (87))))) (.branch 81 (.branch 79 (.leaf (88)) (.branch 80 (.leaf (90)) (.leaf (91)))) (.branch 82 (.leaf (60)) (.branch 83 (.leaf (65)) (.leaf (92)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (93)) (.branch 86 (.leaf (55)) (.leaf (73)))) (.branch 88 (.leaf (57)) (.branch 89 (.leaf (94)) (.leaf (95))))) (.branch 93 (.branch 91 (.leaf (63)) (.branch 92 (.leaf (80)) (.leaf (71)))) (.branch 94 (.leaf (84)) (.branch 95 (.leaf (78)) (.leaf (89)))))))))
noncomputable def originalT (p : Fin 96) : Fin 96 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 48) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (6)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (3)) (.branch 14 (.leaf (4)) (.leaf (5)))) (.branch 16 (.leaf (7)) (.branch 17 (.leaf (8)) (.leaf (8))))) (.branch 21 (.branch 19 (.leaf (9)) (.branch 20 (.leaf (10)) (.leaf (9)))) (.branch 22 (.leaf (10)) (.branch 23 (.leaf (11)) (.leaf (12))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (11)) (.branch 26 (.leaf (12)) (.leaf (13)))) (.branch 28 (.leaf (14)) (.branch 29 (.leaf (15)) (.leaf (13))))) (.branch 33 (.branch 31 (.leaf (14)) (.branch 32 (.leaf (15)) (.leaf (16)))) (.branch 34 (.leaf (17)) (.branch 35 (.leaf (18)) (.leaf (19)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (20)) (.branch 38 (.leaf (16)) (.leaf (17)))) (.branch 40 (.leaf (18)) (.branch 41 (.leaf (19)) (.leaf (20))))) (.branch 45 (.branch 43 (.leaf (21)) (.branch 44 (.leaf (22)) (.leaf (23)))) (.branch 46 (.leaf (24)) (.branch 47 (.leaf (25)) (.leaf (26)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (21)) (.branch 50 (.leaf (22)) (.leaf (23)))) (.branch 52 (.leaf (24)) (.branch 53 (.leaf (25)) (.leaf (26))))) (.branch 57 (.branch 55 (.leaf (27)) (.branch 56 (.leaf (28)) (.leaf (29)))) (.branch 58 (.leaf (30)) (.branch 59 (.leaf (31)) (.leaf (32)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (33)) (.branch 62 (.leaf (34)) (.leaf (27)))) (.branch 64 (.leaf (28)) (.branch 65 (.leaf (29)) (.leaf (30))))) (.branch 69 (.branch 67 (.leaf (31)) (.branch 68 (.leaf (32)) (.leaf (33)))) (.branch 70 (.leaf (34)) (.branch 71 (.leaf (35)) (.leaf (36))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (37)) (.branch 74 (.leaf (38)) (.leaf (39)))) (.branch 76 (.leaf (40)) (.branch 77 (.leaf (40)) (.leaf (35))))) (.branch 81 (.branch 79 (.leaf (36)) (.branch 80 (.leaf (37)) (.leaf (38)))) (.branch 82 (.leaf (39)) (.branch 83 (.leaf (41)) (.leaf (42)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (43)) (.branch 86 (.leaf (44)) (.leaf (45)))) (.branch 88 (.leaf (41)) (.branch 89 (.leaf (42)) (.leaf (43))))) (.branch 93 (.branch 91 (.leaf (44)) (.branch 92 (.leaf (45)) (.leaf (46)))) (.branch 94 (.leaf (47)) (.branch 95 (.leaf (46)) (.leaf (47)))))))))
noncomputable def projection (p : Fin 96) : Fin 48 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 96) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (16)))) (.branch 10 (.leaf (18)) (.branch 11 (.leaf (19)) (.leaf (22)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (23)) (.branch 14 (.leaf (26)) (.leaf (27)))) (.branch 16 (.leaf (28)) (.branch 17 (.leaf (32)) (.leaf (33))))) (.branch 21 (.branch 19 (.leaf (34)) (.branch 20 (.leaf (35)) (.leaf (36)))) (.branch 22 (.leaf (42)) (.branch 23 (.leaf (43)) (.leaf (44))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (45)) (.branch 26 (.leaf (46)) (.leaf (47)))) (.branch 28 (.leaf (54)) (.branch 29 (.leaf (55)) (.leaf (56))))) (.branch 33 (.branch 31 (.leaf (57)) (.branch 32 (.leaf (58)) (.leaf (59)))) (.branch 34 (.leaf (60)) (.branch 35 (.leaf (61)) (.leaf (70)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (71)) (.branch 38 (.leaf (72)) (.leaf (73)))) (.branch 40 (.leaf (74)) (.branch 41 (.leaf (75)) (.leaf (82))))) (.branch 45 (.branch 43 (.leaf (83)) (.branch 44 (.leaf (84)) (.leaf (85)))) (.branch 46 (.leaf (86)) (.branch 47 (.leaf (92)) (.leaf (93))))))))
noncomputable def representative (p : Fin 48) : Fin 96 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (5)) (.leaf (9)))) (.branch 10 (.leaf (8)) (.branch 11 (.leaf (11)) (.leaf (10)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (14)) (.branch 14 (.leaf (16)) (.leaf (12)))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (13)) (.leaf (21))))) (.branch 21 (.branch 19 (.leaf (22)) (.branch 20 (.leaf (15)) (.leaf (25)))) (.branch 22 (.leaf (17)) (.branch 23 (.leaf (18)) (.leaf (28))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (30)) (.branch 26 (.leaf (20)) (.leaf (33)))) (.branch 28 (.leaf (34)) (.branch 29 (.leaf (23)) (.leaf (36))))) (.branch 33 (.branch 31 (.leaf (24)) (.branch 32 (.leaf (38)) (.leaf (40)))) (.branch 34 (.leaf (26)) (.branch 35 (.leaf (27)) (.leaf (39)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (29)) (.branch 38 (.leaf (43)) (.leaf (31)))) (.branch 40 (.leaf (35)) (.branch 41 (.leaf (32)) (.leaf (45))))) (.branch 45 (.branch 43 (.leaf (44)) (.branch 44 (.leaf (37)) (.leaf (42)))) (.branch 46 (.leaf (41)) (.branch 47 (.leaf (47)) (.leaf (46))))))))
noncomputable def S (p : Fin 48) : Fin 48 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (0))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (8)) (.leaf (10)))) (.branch 10 (.leaf (4)) (.branch 11 (.leaf (12)) (.leaf (13)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (15)) (.branch 14 (.leaf (17)) (.leaf (18)))) (.branch 16 (.leaf (20)) (.branch 17 (.leaf (9)) (.leaf (22))))) (.branch 21 (.branch 19 (.leaf (23)) (.branch 20 (.leaf (24)) (.leaf (26)))) (.branch 22 (.leaf (27)) (.branch 23 (.leaf (11)) (.leaf (29))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (31)) (.branch 26 (.leaf (32)) (.leaf (34)))) (.branch 28 (.leaf (35)) (.branch 29 (.leaf (21)) (.leaf (37))))) (.branch 33 (.branch 31 (.leaf (14)) (.branch 32 (.leaf (39)) (.leaf (25)))) (.branch 34 (.leaf (40)) (.branch 35 (.leaf (16)) (.leaf (41)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (42)) (.branch 38 (.leaf (44)) (.leaf (45)))) (.branch 40 (.leaf (33)) (.branch 41 (.leaf (19)) (.leaf (30))))) (.branch 45 (.branch 43 (.leaf (46)) (.branch 44 (.leaf (47)) (.leaf (28)))) (.branch 46 (.leaf (38)) (.branch 47 (.leaf (36)) (.leaf (43))))))))
noncomputable def T (p : Fin 48) : Fin 48 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (5)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (9)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (6)) (.leaf (7)))) (.branch 10 (.leaf (16)) (.branch 11 (.leaf (8)) (.leaf (22)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (10)) (.branch 14 (.leaf (11)) (.leaf (30)))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (34)) (.leaf (13))))) (.branch 21 (.branch 19 (.leaf (14)) (.branch 20 (.leaf (40)) (.leaf (15)))) (.branch 22 (.leaf (28)) (.branch 23 (.leaf (17)) (.leaf (18))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (19)) (.branch 26 (.leaf (32)) (.leaf (20)))) (.branch 28 (.leaf (21)) (.branch 29 (.leaf (44)) (.leaf (23))))) (.branch 33 (.branch 31 (.leaf (41)) (.branch 32 (.leaf (24)) (.leaf (25)))) (.branch 34 (.leaf (39)) (.branch 35 (.leaf (26)) (.leaf (27)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (46)) (.branch 38 (.leaf (29)) (.leaf (45)))) (.branch 40 (.leaf (31)) (.branch 41 (.leaf (33)) (.leaf (35))))) (.branch 45 (.branch 43 (.leaf (36)) (.branch 44 (.leaf (47)) (.leaf (37)))) (.branch 46 (.leaf (38)) (.branch 47 (.leaf (42)) (.leaf (43))))))))
noncomputable def Ti (p : Fin 48) : Fin 48 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 48) : Fin 48 := T (S p)
theorem quotient_relations : (∀ p : Fin 48, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 96, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 96, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 48, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 48)) := [[0,3,7],[1,2,6],[4,5,8],[9,10,13],[11,12,18],[14,15,24],[16,17,27],[19,20,32],[21,22,23],[25,26,40],[28,29,42],[30,31,45],[33,34,35],[36,37,47],[38,39,41],[43,44,46]]
noncomputable def verticesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (2)) (.leaf (8)))) (.branch 10 (.leaf (9)) (.branch 11 (.leaf (10)) (.leaf (12)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (13)) (.branch 14 (.leaf (11)) (.leaf (15)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (18)) (.leaf (19))))) (.branch 21 (.branch 19 (.leaf (14)) (.branch 20 (.leaf (21)) (.leaf (22)))) (.branch 22 (.leaf (24)) (.branch 23 (.leaf (25)) (.leaf (26))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (17)) (.branch 26 (.leaf (27)) (.leaf (28)))) (.branch 28 (.leaf (20)) (.branch 29 (.leaf (30)) (.leaf (31))))) (.branch 33 (.branch 31 (.leaf (33)) (.branch 32 (.leaf (34)) (.leaf (23)))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (37)) (.leaf (38)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (39)) (.branch 38 (.leaf (40)) (.leaf (42)))) (.branch 40 (.leaf (43)) (.branch 41 (.leaf (29)) (.leaf (44))))) (.branch 45 (.branch 43 (.leaf (32)) (.branch 44 (.leaf (45)) (.leaf (46)))) (.branch 46 (.leaf (35)) (.branch 47 (.leaf (47)) (.leaf (41))))))))
noncomputable def verticesIndex (p : Fin 48) : Fin 48 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (7)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (8)))) (.branch 10 (.leaf (9)) (.branch 11 (.leaf (10)) (.leaf (13)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (11)) (.branch 14 (.leaf (12)) (.leaf (18)))) (.branch 16 (.leaf (14)) (.branch 17 (.leaf (15)) (.leaf (24))))) (.branch 21 (.branch 19 (.leaf (16)) (.branch 20 (.leaf (17)) (.leaf (27)))) (.branch 22 (.leaf (19)) (.branch 23 (.leaf (20)) (.leaf (32))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (21)) (.branch 26 (.leaf (22)) (.leaf (23)))) (.branch 28 (.leaf (25)) (.branch 29 (.leaf (26)) (.leaf (40))))) (.branch 33 (.branch 31 (.leaf (28)) (.branch 32 (.leaf (29)) (.leaf (42)))) (.branch 34 (.leaf (30)) (.branch 35 (.leaf (31)) (.leaf (45)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (33)) (.branch 38 (.leaf (34)) (.leaf (35)))) (.branch 40 (.leaf (36)) (.branch 41 (.leaf (37)) (.leaf (47))))) (.branch 45 (.branch 43 (.leaf (38)) (.branch 44 (.leaf (39)) (.leaf (41)))) (.branch 46 (.leaf (43)) (.branch 47 (.leaf (44)) (.leaf (46))))))))
noncomputable def verticesBack (p : Fin 48) : Fin 48 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 48, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 48 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 48, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 48)) := [[0,1],[2,4],[3,6],[5,7],[8,9],[10,11],[12,14],[13,16],[15,19],[17,21],[18,22],[20,25],[23,28],[24,30],[26,33],[27,34],[29,36],[31,38],[32,40],[35,39],[37,43],[41,45],[42,44],[46,47]]
noncomputable def edgesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (7)) (.leaf (8)))) (.branch 10 (.leaf (9)) (.branch 11 (.leaf (10)) (.leaf (11)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (12)) (.branch 14 (.leaf (14)) (.leaf (13)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (15)) (.leaf (18))))) (.branch 21 (.branch 19 (.leaf (20)) (.branch 20 (.leaf (17)) (.leaf (22)))) (.branch 22 (.leaf (19)) (.branch 23 (.leaf (21)) (.leaf (24))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (26)) (.branch 26 (.leaf (23)) (.leaf (28)))) (.branch 28 (.leaf (30)) (.branch 29 (.leaf (25)) (.leaf (32))))) (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (34)) (.leaf (36)))) (.branch 34 (.leaf (29)) (.branch 35 (.leaf (31)) (.leaf (38)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (33)) (.branch 38 (.leaf (40)) (.leaf (35)))) (.branch 40 (.leaf (39)) (.branch 41 (.leaf (37)) (.leaf (42))))) (.branch 45 (.branch 43 (.leaf (44)) (.branch 44 (.leaf (41)) (.leaf (45)))) (.branch 46 (.leaf (43)) (.branch 47 (.leaf (46)) (.leaf (47))))))))
noncomputable def edgesIndex (p : Fin 48) : Fin 48 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (7)) (.leaf (8)))) (.branch 10 (.leaf (9)) (.branch 11 (.leaf (10)) (.leaf (11)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (12)) (.branch 14 (.leaf (14)) (.leaf (13)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (15)) (.leaf (19))))) (.branch 21 (.branch 19 (.leaf (17)) (.branch 20 (.leaf (21)) (.leaf (18)))) (.branch 22 (.leaf (22)) (.branch 23 (.leaf (20)) (.leaf (25))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (23)) (.branch 26 (.leaf (28)) (.leaf (24)))) (.branch 28 (.leaf (30)) (.branch 29 (.leaf (26)) (.leaf (33))))) (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (34)) (.leaf (29)))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (31)) (.leaf (38)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (32)) (.branch 38 (.leaf (40)) (.leaf (35)))) (.branch 40 (.leaf (39)) (.branch 41 (.leaf (37)) (.leaf (43))))) (.branch 45 (.branch 43 (.leaf (41)) (.branch 44 (.leaf (45)) (.leaf (42)))) (.branch 46 (.leaf (44)) (.branch 47 (.leaf (46)) (.leaf (47))))))))
noncomputable def edgesBack (p : Fin 48) : Fin 48 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 48, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 48 := by decide +kernel
theorem edges_partition : ∀ p : Fin 48, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 48)) := [[0,2,5],[1,3],[4,6,7,8,10,12,15,20,26,34,16,9],[11,13,17,22],[14,18,23,29,37,44,28,21,27,35,41,30],[19,24,31,39,33,40],[25,32],[36,42,46],[38,45],[43,47]]
noncomputable def facesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (1)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (8)))) (.branch 10 (.leaf (16)) (.branch 11 (.leaf (9)) (.leaf (17)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (10)) (.branch 14 (.leaf (18)) (.leaf (21)))) (.branch 16 (.leaf (11)) (.branch 17 (.leaf (15)) (.leaf (19))))) (.branch 21 (.branch 19 (.leaf (22)) (.branch 20 (.leaf (33)) (.leaf (12)))) (.branch 22 (.leaf (28)) (.branch 23 (.leaf (20)) (.leaf (23))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (34)) (.branch 26 (.leaf (39)) (.leaf (13)))) (.branch 28 (.leaf (29)) (.branch 29 (.leaf (27)) (.leaf (24))))) (.branch 33 (.branch 31 (.leaf (32)) (.branch 32 (.leaf (35)) (.leaf (40)))) (.branch 34 (.leaf (37)) (.branch 35 (.leaf (14)) (.leaf (30)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (41)) (.branch 38 (.leaf (25)) (.leaf (44)))) (.branch 40 (.leaf (36)) (.branch 41 (.leaf (38)) (.leaf (31))))) (.branch 45 (.branch 43 (.leaf (42)) (.branch 44 (.leaf (46)) (.leaf (26)))) (.branch 46 (.leaf (45)) (.branch 47 (.leaf (43)) (.leaf (47))))))))
noncomputable def facesIndex (p : Fin 48) : Fin 48 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (8)))) (.branch 10 (.leaf (10)) (.branch 11 (.leaf (12)) (.leaf (15)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (20)) (.branch 14 (.leaf (26)) (.leaf (34)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (9)) (.leaf (11))))) (.branch 21 (.branch 19 (.leaf (13)) (.branch 20 (.leaf (17)) (.leaf (22)))) (.branch 22 (.leaf (14)) (.branch 23 (.leaf (18)) (.leaf (23))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (29)) (.branch 26 (.leaf (37)) (.leaf (44)))) (.branch 28 (.leaf (28)) (.branch 29 (.leaf (21)) (.leaf (27))))) (.branch 33 (.branch 31 (.leaf (35)) (.branch 32 (.leaf (41)) (.leaf (30)))) (.branch 34 (.leaf (19)) (.branch 35 (.leaf (24)) (.leaf (31)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (39)) (.branch 38 (.leaf (33)) (.leaf (40)))) (.branch 40 (.leaf (25)) (.branch 41 (.leaf (32)) (.leaf (36))))) (.branch 45 (.branch 43 (.leaf (42)) (.branch 44 (.leaf (46)) (.leaf (38)))) (.branch 46 (.leaf (45)) (.branch 47 (.leaf (43)) (.leaf (47))))))))
noncomputable def facesBack (p : Fin 48) : Fin 48 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 48, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 48 := by decide +kernel
theorem faces_partition : ∀ p : Fin 48, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [3,2,12,4,12,6,2,3,2,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 16 - 24 + 10 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,0,-1,-1⟩)) (.branch 8 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨2,1,1,1⟩)))) (.branch 10 (.leaf (⟨1,-2,1,-1⟩)) (.branch 11 (.leaf (⟨-2,-3,-1,-2⟩)) (.leaf (⟨-3,2,-2,1⟩)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (⟨2,5,1,3⟩)) (.branch 14 (.leaf (⟨-3,-1,-2,-1⟩)) (.leaf (⟨5,-2,3,-1⟩)))) (.branch 16 (.leaf (⟨-2,-7,-1,-4⟩)) (.branch 17 (.leaf (⟨-1,3,-1,2⟩)) (.leaf (⟨3,4,2,3⟩))))) (.branch 21 (.branch 19 (.leaf (⟨5,3,3,2⟩)) (.branch 20 (.leaf (⟨-7,2,-4,1⟩)) (.leaf (⟨2,9,1,5⟩)))) (.branch 22 (.leaf (⟨-8,-3,-5,-2⟩)) (.branch 23 (.leaf (⟨3,-5,2,-3⟩)) (.leaf (⟨-5,-8,-3,-5⟩))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (⟨-7,-5,-4,-3⟩)) (.branch 26 (.leaf (⟨6,1,5,1⟩)) (.leaf (⟨-1,5,-1,4⟩)))) (.branch 28 (.leaf (⟨4,1,3,1⟩)) (.branch 29 (.leaf (⟨-8,5,-5,3⟩)) (.leaf (⟨5,13,3,8⟩))))) (.branch 33 (.branch 31 (.leaf (⟨-5,7,-3,4⟩)) (.branch 32 (.leaf (⟨7,12,4,7⟩)) (.leaf (⟨9,7,5,4⟩)))) (.branch 34 (.leaf (⟨-5,-1,-4,-1⟩)) (.branch 35 (.leaf (⟨1,-4,1,-3⟩)) (.leaf (⟨-4,-5,-3,-4⟩)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (⟨13,-5,8,-3⟩)) (.branch 38 (.leaf (⟨-5,-18,-3,-11⟩)) (.leaf (⟨9,5,7,4⟩)))) (.branch 40 (.leaf (⟨-5,4,-4,3⟩)) (.branch 41 (.leaf (⟨5,6,4,5⟩)) (.leaf (⟨4,9,3,7⟩))))) (.branch 45 (.branch 43 (.leaf (⟨13,8,8,5⟩)) (.branch 44 (.leaf (⟨-21,-8,-13,-5⟩)) (.leaf (⟨8,-13,5,-8⟩)))) (.branch 46 (.leaf (⟨12,5,7,3⟩)) (.branch 47 (.leaf (⟨-13,-21,-8,-13⟩)) (.leaf (⟨-18,-13,-11,-8⟩))))))))
noncomputable def liftMatrix (p : Fin 48) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 48) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],6⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],7⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],8⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],9⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],10⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],11⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],12⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],13⟩,⟨⟨5,-2,3,-1⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],14⟩,⟨⟨-2,-7,-1,-4⟩,[.t (2),.s,.t (4)],15⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],16⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],17⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],18⟩,⟨⟨-7,2,-4,1⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],19⟩,⟨⟨2,9,1,5⟩,[.t (2),.s,.t (5)],20⟩,⟨⟨-8,-3,-5,-2⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (0)],21⟩,⟨⟨3,-5,2,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2)],22⟩,⟨⟨-5,-8,-3,-5⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (1)],23⟩,⟨⟨-7,-5,-4,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],24⟩,⟨⟨6,1,5,1⟩,[.t (1),.s,.t (-5),.s,.t (0)],25⟩,⟨⟨-1,5,-1,4⟩,[.t (1),.s,.t (-4)],26⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],27⟩,⟨⟨-8,5,-5,3⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-1)],28⟩,⟨⟨5,13,3,8⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (2)],29⟩,⟨⟨-5,7,-3,4⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2)],30⟩,⟨⟨7,12,4,7⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],31⟩,⟨⟨9,7,5,4⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],32⟩,⟨⟨-5,-1,-4,-1⟩,[.t (1),.s,.t (-4),.s,.t (0)],33⟩,⟨⟨1,-4,1,-3⟩,[.t (1),.s,.t (-3)],34⟩,⟨⟨-4,-5,-3,-4⟩,[.t (1),.s,.t (-3),.s,.t (1)],35⟩,⟨⟨13,-5,8,-3⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],36⟩,⟨⟨-5,-18,-3,-11⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (3)],37⟩,⟨⟨9,5,7,4⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (0)],38⟩,⟨⟨-5,4,-4,3⟩,[.t (1),.s,.t (-4),.s,.t (-1)],39⟩,⟨⟨5,6,4,5⟩,[.t (1),.s,.t (-4),.s,.t (1)],40⟩,⟨⟨4,9,3,7⟩,[.t (1),.s,.t (-3),.s,.t (2)],41⟩,⟨⟨13,8,8,5⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],42⟩,⟨⟨-21,-8,-13,-5⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (0)],43⟩,⟨⟨8,-13,5,-8⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2)],44⟩,⟨⟨12,5,7,3⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],45⟩,⟨⟨-13,-21,-8,-13⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (1)],46⟩,⟨⟨-18,-13,-11,-8⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],47⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 48 ∧ ((List.finRange 48).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 48) := [⟨7,2,⟨⟨-1,-3,0,-1⟩,[.t (3)],0⟩⟩,⟨3,1,⟨⟨-1,0,-2,-1⟩,[.t (0),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨6,1,⟨⟨-1,0,2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨25,4,⟨⟨-19,21,-10,11⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨40,6,⟨⟨-71,87,-40,49⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨38,5,⟨⟨-97,123,-56,71⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨41,8,⟨⟨71,-93,42,-55⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨17,3,⟨⟨-25,36,-16,23⟩,[.t (1),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨21,3,⟨⟨23,-36,16,-25⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨43,7,⟨⟨-155,249,-94,151⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨46,9,⟨⟨313,-507,192,-311⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨47,9,⟨⟨-311,507,-192,313⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨37,7,⟨⟨151,-249,94,-155⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-7),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨45,8,⟨⟨-55,93,-42,71⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2)],0⟩⟩,⟨31,5,⟨⟨71,-123,56,-97⟩,[.t (1),.s,.t (-4),.s,.t (-4),.s,.t (-4),.s,.t (-2)],0⟩⟩,⟨32,6,⟨⟨49,-87,40,-71⟩,[.t (1),.s,.t (-5),.s,.t (-2),.s,.t (-5),.s,.t (-2)],0⟩⟩,⟨20,4,⟨⟨11,-21,10,-19⟩,[.t (1),.s,.t (-10),.s,.t (-2)],0⟩⟩,⟨5,2,⟨⟨-1,3,0,-1⟩,[.t (-3)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(0,1),(1,1),(6,5),(5,4),(9,7),(4,3),(3,2),(8,5),(21,13),(13,8),(18,11),(5,3),(12,7),(7,4),(9,5),(2,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G192_194_c0

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
