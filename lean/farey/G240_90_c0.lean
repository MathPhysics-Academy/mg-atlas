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
namespace G240_90_c0
noncomputable def originalSData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (8))) (.branch 7 (.leaf (12)) (.branch 8 (.leaf (0)) (.leaf (15)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (14)) (.leaf (18))) (.branch 12 (.leaf (20)) (.leaf (16)))) (.branch 15 (.branch 14 (.leaf (23)) (.leaf (25))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (28)) (.leaf (30))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (26)) (.leaf (33))) (.branch 21 (.leaf (27)) (.leaf (34)))) (.branch 24 (.branch 23 (.leaf (35)) (.leaf (29))) (.branch 25 (.leaf (38)) (.branch 26 (.leaf (4)) (.leaf (41)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (43)) (.leaf (6))) (.branch 30 (.leaf (46)) (.leaf (40)))) (.branch 33 (.branch 32 (.leaf (48)) (.leaf (49))) (.branch 34 (.leaf (42)) (.branch 35 (.leaf (44)) (.leaf (45)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (53)) (.leaf (55))) (.branch 39 (.leaf (47)) (.leaf (17)))) (.branch 42 (.branch 41 (.leaf (39)) (.leaf (10))) (.branch 43 (.leaf (52)) (.branch 44 (.leaf (11)) (.leaf (51)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (59)) (.leaf (13))) (.branch 48 (.leaf (62)) (.leaf (57)))) (.branch 51 (.branch 50 (.leaf (58)) (.leaf (54))) (.branch 52 (.leaf (21)) (.branch 53 (.leaf (19)) (.leaf (60))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (65)) (.leaf (61))) (.branch 57 (.leaf (31)) (.leaf (56)))) (.branch 60 (.branch 59 (.leaf (67)) (.leaf (22))) (.branch 61 (.leaf (68)) (.branch 62 (.leaf (66)) (.leaf (24)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (70)) (.leaf (63))) (.branch 66 (.leaf (69)) (.leaf (37)))) (.branch 69 (.branch 68 (.leaf (32)) (.leaf (36))) (.branch 70 (.leaf (50)) (.branch 71 (.leaf (71)) (.leaf (64)))))))))
noncomputable def originalS (p : Fin 72) : Fin 72 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (10)) (.leaf (11))) (.branch 7 (.leaf (13)) (.branch 8 (.leaf (14)) (.leaf (16)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (17)) (.leaf (19))) (.branch 12 (.leaf (21)) (.leaf (22)))) (.branch 15 (.branch 14 (.leaf (24)) (.leaf (26))) (.branch 16 (.leaf (27)) (.branch 17 (.leaf (29)) (.leaf (31))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (32)) (.leaf (20))) (.branch 21 (.leaf (1)) (.leaf (18)))) (.branch 24 (.branch 23 (.leaf (36)) (.leaf (37))) (.branch 25 (.leaf (39)) (.branch 26 (.leaf (40)) (.leaf (42)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (44)) (.leaf (45))) (.branch 30 (.leaf (47)) (.leaf (3)))) (.branch 33 (.branch 32 (.leaf (23)) (.leaf (50))) (.branch 34 (.leaf (51)) (.branch 35 (.leaf (52)) (.leaf (5)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (54)) (.leaf (49))) (.branch 39 (.leaf (56)) (.leaf (0)))) (.branch 42 (.branch 41 (.leaf (57)) (.leaf (58))) (.branch 43 (.leaf (43)) (.branch 44 (.leaf (7)) (.leaf (41)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (60)) (.leaf (61))) (.branch 48 (.leaf (30)) (.leaf (38)))) (.branch 51 (.branch 50 (.leaf (9)) (.leaf (63))) (.branch 52 (.leaf (33)) (.branch 53 (.leaf (34)) (.leaf (64))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (66)) (.leaf (12))) (.branch 57 (.leaf (62)) (.leaf (46)))) (.branch 60 (.branch 59 (.leaf (65)) (.leaf (15))) (.branch 61 (.leaf (69)) (.branch 62 (.leaf (67)) (.leaf (48)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (35)) (.leaf (53))) (.branch 66 (.leaf (71)) (.leaf (28)))) (.branch 69 (.branch 68 (.leaf (25)) (.leaf (70))) (.branch 70 (.leaf (55)) (.branch 71 (.leaf (68)) (.leaf (59)))))))))
noncomputable def originalT (p : Fin 72) : Fin 72 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 36) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (8)) (.leaf (9)))) (.branch 15 (.branch 14 (.leaf (10)) (.leaf (3))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (5)) (.leaf (11))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (12)) (.leaf (13))) (.branch 21 (.leaf (14)) (.leaf (15)))) (.branch 24 (.branch 23 (.leaf (16)) (.leaf (17))) (.branch 25 (.leaf (18)) (.branch 26 (.leaf (6)) (.leaf (7)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (8)) (.leaf (9))) (.branch 30 (.leaf (10)) (.leaf (19)))) (.branch 33 (.branch 32 (.leaf (20)) (.leaf (21))) (.branch 34 (.leaf (22)) (.branch 35 (.leaf (23)) (.leaf (24)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (25)) (.leaf (26))) (.branch 39 (.leaf (27)) (.leaf (19)))) (.branch 42 (.branch 41 (.leaf (11)) (.leaf (12))) (.branch 43 (.leaf (13)) (.branch 44 (.leaf (14)) (.leaf (15)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (16)) (.leaf (17))) (.branch 48 (.leaf (18)) (.leaf (28)))) (.branch 51 (.branch 50 (.leaf (29)) (.leaf (30))) (.branch 52 (.leaf (23)) (.branch 53 (.leaf (22)) (.leaf (31))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (32)) (.leaf (33))) (.branch 57 (.leaf (28)) (.leaf (20)))) (.branch 60 (.branch 59 (.leaf (21)) (.leaf (24))) (.branch 61 (.leaf (25)) (.branch 62 (.leaf (26)) (.leaf (27)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (34)) (.leaf (35))) (.branch 66 (.leaf (30)) (.leaf (33)))) (.branch 69 (.branch 68 (.leaf (29)) (.leaf (31))) (.branch 70 (.leaf (32)) (.branch 71 (.leaf (35)) (.leaf (34)))))))))
noncomputable def projection (p : Fin 72) : Fin 36 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 72) :=
  (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (6))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (11)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (17)) (.leaf (18)))) (.branch 15 (.branch 14 (.leaf (19)) (.leaf (20))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (22)) (.leaf (23))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (24)) (.leaf (30))) (.branch 21 (.leaf (31)) (.leaf (32)))) (.branch 24 (.branch 23 (.leaf (33)) (.leaf (34))) (.branch 25 (.leaf (35)) (.branch 26 (.leaf (36)) (.leaf (37)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (38)) (.leaf (48))) (.branch 30 (.leaf (49)) (.leaf (50)))) (.branch 33 (.branch 32 (.leaf (53)) (.leaf (54))) (.branch 34 (.leaf (55)) (.branch 35 (.leaf (63)) (.leaf (64))))))))
noncomputable def representative (p : Fin 36) : Fin 72 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 36) :=
  (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (14)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (17))) (.branch 12 (.leaf (19)) (.leaf (7)))) (.branch 15 (.branch 14 (.leaf (22)) (.leaf (8))) (.branch 16 (.leaf (23)) (.branch 17 (.leaf (24)) (.leaf (10))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (27)) (.leaf (11))) (.branch 21 (.leaf (28)) (.leaf (29)))) (.branch 24 (.branch 23 (.leaf (13)) (.leaf (15))) (.branch 25 (.leaf (16)) (.branch 26 (.leaf (31)) (.leaf (33)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (18)) (.leaf (20))) (.branch 30 (.leaf (21)) (.leaf (32)))) (.branch 33 (.branch 32 (.leaf (25)) (.leaf (30))) (.branch 34 (.leaf (26)) (.branch 35 (.leaf (35)) (.leaf (34))))))))
noncomputable def S (p : Fin 36) : Fin 36 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 36) :=
  (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (10))) (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (15)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (16)) (.leaf (18))) (.branch 12 (.leaf (20)) (.leaf (21)))) (.branch 15 (.branch 14 (.leaf (14)) (.leaf (1))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (25)) (.leaf (26))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (19)) (.leaf (0))) (.branch 21 (.leaf (17)) (.leaf (30)))) (.branch 24 (.branch 23 (.leaf (23)) (.leaf (22))) (.branch 25 (.leaf (4)) (.branch 26 (.leaf (32)) (.leaf (29)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (28)) (.leaf (27))) (.branch 30 (.leaf (6)) (.leaf (34)))) (.branch 33 (.branch 32 (.leaf (35)) (.leaf (33))) (.branch 34 (.leaf (9)) (.branch 35 (.leaf (24)) (.leaf (31))))))))
noncomputable def T (p : Fin 36) : Fin 36 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 36) :=
  (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (19)) (.leaf (14))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (24)) (.leaf (2))) (.branch 7 (.leaf (29)) (.branch 8 (.leaf (3)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (33)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (15)))) (.branch 15 (.branch 14 (.leaf (7)) (.leaf (13))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (20))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (10)) (.leaf (18))) (.branch 21 (.leaf (11)) (.leaf (12)))) (.branch 24 (.branch 23 (.leaf (23)) (.leaf (22))) (.branch 25 (.leaf (34)) (.branch 26 (.leaf (16)) (.leaf (17)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (28)) (.leaf (27))) (.branch 30 (.leaf (26)) (.leaf (21)))) (.branch 33 (.branch 32 (.leaf (35)) (.leaf (25))) (.branch 34 (.leaf (32)) (.branch 35 (.leaf (30)) (.leaf (31))))))))
noncomputable def Ti (p : Fin 36) : Fin 36 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 36) : Fin 36 := T (S p)
theorem quotient_relations : (∀ p : Fin 36, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 72, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 72, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 36, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 36)) := [[0,3,11],[1,2,8],[4,5,16],[6,7,21],[9,10,26],[12,13,23],[14,15,22],[17,18,28],[19,20,27],[24,25,35],[29,30,33],[31,32,34]]
noncomputable def verticesIndexData : LookupTree (Fin 36) :=
 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (2)) (.leaf (15)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (18))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (8)) (.leaf (21))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (22)) (.leaf (24))) (.branch 21 (.leaf (25)) (.leaf (11)))) (.branch 24 (.branch 23 (.leaf (20)) (.leaf (17))) (.branch 25 (.leaf (27)) (.branch 26 (.leaf (28)) (.leaf (14)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (26)) (.leaf (23))) (.branch 30 (.leaf (30)) (.leaf (31)))) (.branch 33 (.branch 32 (.leaf (33)) (.leaf (34))) (.branch 34 (.leaf (32)) (.branch 35 (.leaf (35)) (.leaf (29))))))))
noncomputable def verticesIndex (p : Fin 36) : Fin 36 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 36) :=
 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (11)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (16)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (21)) (.leaf (9)))) (.branch 15 (.branch 14 (.leaf (10)) (.leaf (26))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (23))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (14)) (.leaf (15))) (.branch 21 (.leaf (22)) (.leaf (17)))) (.branch 24 (.branch 23 (.leaf (18)) (.leaf (28))) (.branch 25 (.leaf (19)) (.branch 26 (.leaf (20)) (.leaf (27)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (24)) (.leaf (25))) (.branch 30 (.leaf (35)) (.leaf (29)))) (.branch 33 (.branch 32 (.leaf (30)) (.leaf (33))) (.branch 34 (.leaf (31)) (.branch 35 (.leaf (32)) (.leaf (34))))))))
noncomputable def verticesBack (p : Fin 36) : Fin 36 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 36, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 36 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 36, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 36)) := [[0,1],[2,4],[3,6],[5,9],[7,12],[8,14],[10,17],[11,19],[13,22],[15,23],[16,24],[18,27],[20,28],[21,29],[25,31],[26,33],[30,32],[34,35]]
noncomputable def edgesIndexData : LookupTree (Fin 36) :=
 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (10)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (7)) (.leaf (12))) (.branch 12 (.leaf (14)) (.leaf (9)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (11))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (20)) (.leaf (13))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (22)) (.leaf (15))) (.branch 21 (.leaf (24)) (.leaf (26)))) (.branch 24 (.branch 23 (.leaf (17)) (.leaf (19))) (.branch 25 (.leaf (21)) (.branch 26 (.leaf (28)) (.leaf (30)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (23)) (.leaf (25))) (.branch 30 (.leaf (27)) (.leaf (32)))) (.branch 33 (.branch 32 (.leaf (29)) (.leaf (33))) (.branch 34 (.leaf (31)) (.branch 35 (.leaf (34)) (.leaf (35))))))))
noncomputable def edgesIndex (p : Fin 36) : Fin 36 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 36) :=
 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (12)) (.leaf (8))) (.branch 12 (.leaf (14)) (.leaf (10)))) (.branch 15 (.branch 14 (.leaf (17)) (.leaf (11))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (13)) (.leaf (22))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (15)) (.leaf (23))) (.branch 21 (.leaf (16)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (18)) (.leaf (27))) (.branch 25 (.leaf (20)) (.branch 26 (.leaf (28)) (.leaf (21)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (29)) (.leaf (25))) (.branch 30 (.leaf (31)) (.leaf (26)))) (.branch 33 (.branch 32 (.leaf (33)) (.leaf (30))) (.branch 34 (.leaf (32)) (.branch 35 (.leaf (34)) (.leaf (35))))))))
noncomputable def edgesBack (p : Fin 36) : Fin 36 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 36, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 36 := by decide +kernel
theorem edges_partition : ∀ p : Fin 36, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 36)) := [[0,2,5,10,18,19],[1,3,7,13,14],[4,8,15,12,21,30,34,24],[6,11,20,17,26,29],[9,16,25,32,33],[22,23],[27,28],[31,35]]
noncomputable def facesIndexData : LookupTree (Fin 36) :=
 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (6))) (.branch 3 (.leaf (1)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (11)) (.leaf (2))) (.branch 7 (.leaf (19)) (.branch 8 (.leaf (8)) (.leaf (12)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (25)) (.leaf (3))) (.branch 12 (.leaf (20)) (.leaf (14)))) (.branch 15 (.branch 14 (.leaf (9)) (.leaf (10))) (.branch 16 (.leaf (13)) (.branch 17 (.leaf (26)) (.leaf (22))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (4)) (.leaf (5))) (.branch 21 (.leaf (21)) (.leaf (15)))) (.branch 24 (.branch 23 (.leaf (30)) (.leaf (31))) (.branch 25 (.leaf (18)) (.branch 26 (.leaf (27)) (.leaf (23)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (32)) (.leaf (33))) (.branch 30 (.leaf (24)) (.leaf (16)))) (.branch 33 (.branch 32 (.leaf (34)) (.leaf (28))) (.branch 34 (.leaf (29)) (.branch 35 (.leaf (17)) (.leaf (35))))))))
noncomputable def facesIndex (p : Fin 36) : Fin 36 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 36) :=
 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (10)))) (.branch 6 (.branch 5 (.leaf (18)) (.leaf (19))) (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (7)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (13)) (.leaf (14))) (.branch 12 (.leaf (4)) (.leaf (8)))) (.branch 15 (.branch 14 (.leaf (15)) (.leaf (12))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (30)) (.leaf (34))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (24)) (.leaf (6))) (.branch 21 (.leaf (11)) (.leaf (20)))) (.branch 24 (.branch 23 (.leaf (17)) (.leaf (26))) (.branch 25 (.leaf (29)) (.branch 26 (.leaf (9)) (.leaf (16)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (25)) (.leaf (32))) (.branch 30 (.leaf (33)) (.leaf (22)))) (.branch 33 (.branch 32 (.leaf (23)) (.leaf (27))) (.branch 34 (.leaf (28)) (.branch 35 (.leaf (31)) (.leaf (35))))))))
noncomputable def facesBack (p : Fin 36) : Fin 36 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 36, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 36 := by decide +kernel
theorem faces_partition : ∀ p : Fin 36, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [6,5,8,6,5,2,2,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 12 - 18 + 8 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.leaf (⟨-1,-3,0,-1⟩))) (.branch 12 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,0,-2,1⟩)))) (.branch 15 (.branch 14 (.leaf (⟨0,-1,1,3⟩)) (.leaf (⟨0,1,-1,1⟩))) (.branch 16 (.leaf (⟨1,1,1,2⟩)) (.branch 17 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨-3,1,-1,0⟩))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (⟨1,4,0,1⟩)) (.leaf (⟨-1,-5,0,-1⟩))) (.branch 21 (.leaf (⟨-5,-4,-1,-1⟩)) (.leaf (⟨1,1,-2,-1⟩)))) (.branch 24 (.branch 23 (.leaf (⟨1,0,2,1⟩)) (.leaf (⟨-1,-1,3,2⟩))) (.branch 25 (.leaf (⟨1,-2,1,-1⟩)) (.branch 26 (.leaf (⟨-2,-3,-1,-2⟩)) (.leaf (⟨-3,-2,-1,-1⟩)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (⟨4,-1,1,0⟩)) (.leaf (⟨4,3,1,1⟩))) (.branch 30 (.leaf (⟨3,5,1,2⟩)) (.leaf (⟨5,2,2,1⟩)))) (.branch 33 (.branch 32 (.leaf (⟨-3,2,-2,1⟩)) (.leaf (⟨2,5,1,3⟩))) (.branch 34 (.leaf (⟨-2,3,-1,1⟩)) (.branch 35 (.leaf (⟨5,3,3,2⟩)) (.leaf (⟨-3,-1,-2,-1⟩))))))))
noncomputable def liftMatrix (p : Fin 36) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 36) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],12⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],13⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],14⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],15⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],16⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],17⟩,⟨⟨1,4,0,1⟩,[.t (4)],18⟩,⟨⟨-1,-5,0,-1⟩,[.t (5)],19⟩,⟨⟨-5,-4,-1,-1⟩,[.t (5),.s,.t (1)],20⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],21⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],22⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],23⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],24⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],25⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],26⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],27⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],28⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],29⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],30⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],31⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],32⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],33⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],34⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],35⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 36 ∧ ((List.finRange 36).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 36) := [⟨11,1,⟨⟨-1,-6,0,-1⟩,[.t (6)],0⟩⟩,⟨21,5,⟨⟨-11,-8,-4,-3⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨23,3,⟨⟨-5,-2,-7,-3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨13,2,⟨⟨1,0,5,1⟩,[.t (0),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨22,2,⟨⟨1,0,-5,1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨15,3,⟨⟨-3,2,7,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨35,7,⟨⟨13,-18,8,-11⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨34,7,⟨⟨-11,18,-8,13⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨32,6,⟨⟨-11,20,-5,9⟩,[.t (2),.s,.t (-5),.s,.t (-2)],0⟩⟩,⟨30,6,⟨⟨9,-20,5,-11⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨29,5,⟨⟨-3,8,4,-11⟩,[.t (-1),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨28,4,⟨⟨9,-32,2,-7⟩,[.t (4),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨20,4,⟨⟨-7,32,-2,9⟩,[.t (3),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨19,1,⟨⟨-1,6,0,-1⟩,[.t (-6)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-1,2),(-1,3),(0,1),(1,2),(1,1),(3,2),(5,3),(2,1),(5,2),(3,1),(4,1),(5,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G240_90_c0

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
