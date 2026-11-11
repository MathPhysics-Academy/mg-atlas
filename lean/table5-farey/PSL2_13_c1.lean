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
namespace PSL2_13_c1
noncomputable def originalSData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (8))) (.branch 7 (.leaf (11)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (13))) (.branch 11 (.leaf (4)) (.leaf (15)))) (.branch 14 (.branch 13 (.leaf (19)) (.leaf (10))) (.branch 15 (.leaf (2)) (.leaf (21)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (23)) (.leaf (25))) (.branch 19 (.leaf (27)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (30)) (.leaf (6))) (.branch 23 (.leaf (32)) (.leaf (17))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (28)) (.leaf (16))) (.branch 27 (.leaf (35)) (.leaf (31)))) (.branch 30 (.branch 29 (.leaf (26)) (.leaf (37))) (.branch 31 (.leaf (33)) (.leaf (40))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (12)) (.leaf (42))) (.branch 35 (.leaf (43)) (.leaf (24)))) (.branch 38 (.branch 37 (.leaf (44)) (.leaf (41))) (.branch 39 (.leaf (45)) (.leaf (47))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (18)) (.leaf (49))) (.branch 43 (.leaf (20)) (.leaf (36)))) (.branch 46 (.branch 45 (.leaf (34)) (.leaf (50))) (.branch 47 (.leaf (53)) (.leaf (51)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (54)) (.leaf (29))) (.branch 51 (.leaf (55)) (.leaf (57)))) (.branch 54 (.branch 53 (.leaf (48)) (.leaf (56))) (.branch 55 (.leaf (58)) (.leaf (38))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (62)) (.leaf (39))) (.branch 59 (.leaf (52)) (.leaf (63)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (60))) (.branch 63 (.leaf (46)) (.leaf (61))))))))
noncomputable def originalS (p : Fin 64) : Fin 64 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (10))) (.branch 7 (.leaf (12)) (.leaf (13))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (15)) (.leaf (16))) (.branch 11 (.leaf (17)) (.leaf (18)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (7))) (.branch 15 (.leaf (9)) (.leaf (22)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (24)) (.leaf (26))) (.branch 19 (.leaf (28)) (.leaf (29)))) (.branch 22 (.branch 21 (.leaf (25)) (.leaf (31))) (.branch 23 (.leaf (33)) (.leaf (3))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (34)) (.leaf (0))) (.branch 27 (.leaf (36)) (.leaf (5)))) (.branch 30 (.branch 29 (.leaf (30)) (.leaf (38))) (.branch 31 (.leaf (39)) (.leaf (35))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (41)) (.leaf (23))) (.branch 35 (.leaf (43)) (.leaf (42)))) (.branch 38 (.branch 37 (.leaf (44)) (.leaf (11))) (.branch 39 (.leaf (46)) (.leaf (48))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (14)) (.leaf (50))) (.branch 43 (.leaf (51)) (.leaf (40)))) (.branch 46 (.branch 45 (.leaf (27)) (.leaf (52))) (.branch 47 (.leaf (53)) (.leaf (19)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (37)) (.leaf (21))) (.branch 51 (.leaf (56)) (.leaf (58)))) (.branch 54 (.branch 53 (.leaf (59)) (.leaf (60))) (.branch 55 (.leaf (61)) (.leaf (54))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (62)) (.leaf (32))) (.branch 59 (.leaf (49)) (.leaf (45)))) (.branch 62 (.branch 61 (.leaf (47)) (.leaf (55))) (.branch 63 (.leaf (63)) (.leaf (57))))))))
noncomputable def originalT (p : Fin 64) : Fin 64 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 32) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (6)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (3))) (.branch 15 (.leaf (4)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (9)) (.leaf (9))) (.branch 19 (.leaf (10)) (.leaf (11)))) (.branch 22 (.branch 21 (.leaf (12)) (.leaf (7))) (.branch 23 (.leaf (8)) (.leaf (13))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (14)) (.leaf (13))) (.branch 27 (.leaf (14)) (.leaf (15)))) (.branch 30 (.branch 29 (.leaf (16)) (.leaf (17))) (.branch 31 (.leaf (18)) (.leaf (10))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (11)) (.leaf (12))) (.branch 35 (.leaf (19)) (.leaf (16)))) (.branch 38 (.branch 37 (.leaf (19)) (.leaf (20))) (.branch 39 (.leaf (21)) (.leaf (22))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (15)) (.leaf (17))) (.branch 43 (.leaf (18)) (.leaf (23)))) (.branch 46 (.branch 45 (.leaf (23)) (.leaf (24))) (.branch 47 (.leaf (25)) (.leaf (26)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (27)) (.leaf (20))) (.branch 51 (.leaf (21)) (.leaf (22)))) (.branch 54 (.branch 53 (.leaf (28)) (.leaf (29))) (.branch 55 (.leaf (28)) (.leaf (24))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (25)) (.leaf (26))) (.branch 59 (.leaf (27)) (.leaf (30)))) (.branch 62 (.branch 61 (.leaf (31)) (.leaf (30))) (.branch 63 (.leaf (29)) (.leaf (31))))))))
noncomputable def projection (p : Fin 64) : Fin 32 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 64) :=
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (6))) (.branch 7 (.leaf (9)) (.leaf (11))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (16))) (.branch 11 (.leaf (18)) (.leaf (19)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (23))) (.branch 15 (.leaf (24)) (.leaf (27)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (28)) (.leaf (29))) (.branch 19 (.leaf (30)) (.leaf (34)))) (.branch 22 (.branch 21 (.leaf (37)) (.leaf (38))) (.branch 23 (.leaf (39)) (.leaf (43))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (45)) (.leaf (46))) (.branch 27 (.leaf (47)) (.leaf (48)))) (.branch 30 (.branch 29 (.leaf (52)) (.leaf (53))) (.branch 31 (.leaf (59)) (.leaf (60)))))))
noncomputable def representative (p : Fin 32) : Fin 64 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 32) :=
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (7))) (.branch 7 (.leaf (3)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (11)) (.leaf (13))) (.branch 11 (.leaf (15)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (18)) (.leaf (9))) (.branch 15 (.leaf (16)) (.leaf (10)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (20))) (.branch 19 (.leaf (12)) (.leaf (23)))) (.branch 22 (.branch 21 (.leaf (17)) (.leaf (24))) (.branch 23 (.leaf (26)) (.leaf (19))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (29))) (.branch 27 (.leaf (22)) (.leaf (28)))) (.branch 30 (.branch 29 (.leaf (27)) (.leaf (25))) (.branch 31 (.leaf (31)) (.leaf (30)))))))
noncomputable def S (p : Fin 32) : Fin 32 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 32) :=
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (8))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (14))) (.branch 11 (.leaf (16)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (13)) (.leaf (0))) (.branch 15 (.leaf (19)) (.leaf (4)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (18)) (.leaf (21))) (.branch 19 (.leaf (22)) (.leaf (23)))) (.branch 22 (.branch 21 (.leaf (7)) (.leaf (25))) (.branch 23 (.leaf (27)) (.leaf (15))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (28)) (.leaf (29))) (.branch 27 (.leaf (11)) (.leaf (20)))) (.branch 30 (.branch 29 (.leaf (30)) (.leaf (31))) (.branch 31 (.leaf (24)) (.leaf (26)))))))
noncomputable def T (p : Fin 32) : Fin 32 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 32) :=
  (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (13)) (.leaf (3))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (15)) (.leaf (2))) (.branch 7 (.leaf (4)) (.leaf (20))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (26)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (12))) (.branch 15 (.leaf (9)) (.leaf (23)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (16)) (.leaf (14)))) (.branch 22 (.branch 21 (.leaf (27)) (.leaf (17))) (.branch 23 (.leaf (18)) (.leaf (19))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (30)) (.leaf (21))) (.branch 27 (.leaf (31)) (.leaf (22)))) (.branch 30 (.branch 29 (.leaf (24)) (.leaf (25))) (.branch 31 (.leaf (28)) (.leaf (29)))))))
noncomputable def Ti (p : Fin 32) : Fin 32 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 32) : Fin 32 := T (S p)
theorem quotient_relations : (∀ p : Fin 32, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 64, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 64, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 32, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 32)) := [[0,3,9],[1,2,6],[4,5,10],[7,8,17],[11,12,22],[13,14,18],[15,16,19],[20,21,28],[23],[24,25,31],[26,27,30],[29]]
noncomputable def verticesIndexData : LookupTree (Fin 32) :=
 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (5)) (.leaf (9))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (2))) (.branch 11 (.leaf (8)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (13)) (.leaf (15))) (.branch 15 (.leaf (16)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (19)) (.leaf (11))) (.branch 19 (.leaf (17)) (.leaf (20)))) (.branch 22 (.branch 21 (.leaf (21)) (.leaf (22))) (.branch 23 (.leaf (14)) (.leaf (24))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (25)) (.leaf (26))) (.branch 27 (.leaf (28)) (.leaf (29)))) (.branch 30 (.branch 29 (.leaf (23)) (.leaf (31))) (.branch 31 (.leaf (30)) (.leaf (27)))))))
noncomputable def verticesIndex (p : Fin 32) : Fin 32 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 32) :=
 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (9)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (7))) (.branch 11 (.leaf (8)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (12))) (.branch 15 (.leaf (22)) (.leaf (13)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (18))) (.branch 19 (.leaf (15)) (.leaf (16)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (20))) (.branch 23 (.leaf (21)) (.leaf (28))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (23)) (.leaf (24))) (.branch 27 (.leaf (25)) (.leaf (31)))) (.branch 30 (.branch 29 (.leaf (26)) (.leaf (27))) (.branch 31 (.leaf (30)) (.leaf (29)))))))
noncomputable def verticesBack (p : Fin 32) : Fin 32 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 32, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 32 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 32, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 32)) := [[0,1],[2,4],[3,6],[5,7],[8,11],[9,13],[10,15],[12,18],[14,16],[17,20],[19,23],[21,24],[22,26],[25,29],[27,28],[30,31]]
noncomputable def edgesIndexData : LookupTree (Fin 32) :=
 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (8)) (.leaf (10))) (.branch 11 (.leaf (12)) (.leaf (9)))) (.branch 14 (.branch 13 (.leaf (14)) (.leaf (11))) (.branch 15 (.leaf (16)) (.leaf (13)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (17)) (.leaf (18))) (.branch 19 (.leaf (15)) (.leaf (20)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (22))) (.branch 23 (.leaf (24)) (.leaf (21))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (23)) (.leaf (26))) (.branch 27 (.leaf (25)) (.leaf (28)))) (.branch 30 (.branch 29 (.leaf (29)) (.leaf (27))) (.branch 31 (.leaf (30)) (.leaf (31)))))))
noncomputable def edgesIndex (p : Fin 32) : Fin 32 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 32) :=
 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (7))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (8)) (.leaf (11))) (.branch 11 (.leaf (9)) (.leaf (13)))) (.branch 14 (.branch 13 (.leaf (10)) (.leaf (15))) (.branch 15 (.leaf (12)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (16))) (.branch 19 (.leaf (17)) (.leaf (20)))) (.branch 22 (.branch 21 (.leaf (19)) (.leaf (23))) (.branch 23 (.leaf (21)) (.leaf (24))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (22)) (.leaf (26))) (.branch 27 (.leaf (25)) (.leaf (29)))) (.branch 30 (.branch 29 (.leaf (27)) (.leaf (28))) (.branch 31 (.leaf (30)) (.leaf (31)))))))
noncomputable def edgesBack (p : Fin 32) : Fin 32 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 32, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 32 := by decide +kernel
theorem edges_partition : ∀ p : Fin 32, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 32)) := [[0,2,5,8,12,13],[1,3],[4,6,9,14,19,23,15],[7,10,16,18,22,27,20],[11,17,21,25,29,31,26],[24,28,30]]
noncomputable def facesIndexData : LookupTree (Fin 32) :=
 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (6))) (.branch 3 (.leaf (1)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (2))) (.branch 7 (.leaf (9)) (.leaf (15))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (3)) (.leaf (10))) (.branch 11 (.leaf (16)) (.leaf (22)))) (.branch 14 (.branch 13 (.leaf (4)) (.leaf (5))) (.branch 15 (.leaf (11)) (.leaf (14)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (17)) (.leaf (23))) (.branch 19 (.leaf (18)) (.leaf (12)))) (.branch 22 (.branch 21 (.leaf (21)) (.leaf (24))) (.branch 23 (.leaf (19)) (.leaf (13))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (29)) (.leaf (25))) (.branch 27 (.leaf (28)) (.leaf (20)))) (.branch 30 (.branch 29 (.leaf (30)) (.leaf (26))) (.branch 31 (.leaf (31)) (.leaf (27)))))))
noncomputable def facesIndex (p : Fin 32) : Fin 32 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 32) :=
 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (12)) (.leaf (13))) (.branch 7 (.leaf (1)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (6))) (.branch 11 (.leaf (9)) (.leaf (14)))) (.branch 14 (.branch 13 (.leaf (19)) (.leaf (23))) (.branch 15 (.leaf (15)) (.leaf (7)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (16))) (.branch 19 (.leaf (18)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (27)) (.leaf (20))) (.branch 23 (.leaf (11)) (.leaf (17))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (25))) (.branch 27 (.leaf (29)) (.leaf (31)))) (.branch 30 (.branch 29 (.leaf (26)) (.leaf (24))) (.branch 31 (.leaf (28)) (.leaf (30)))))))
noncomputable def facesBack (p : Fin 32) : Fin 32 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 32, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 32 := by decide +kernel
theorem faces_partition : ∀ p : Fin 32, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [6,2,7,7,7,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 12 - 16 + 6 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 2 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨2,-1,1,0⟩))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (⟨-1,-3,0,-1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 11 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨-3,1,-1,0⟩)))) (.branch 14 (.branch 13 (.leaf (⟨1,4,0,1⟩)) (.leaf (⟨-1,-5,0,-1⟩))) (.branch 15 (.leaf (⟨-5,-4,-1,-1⟩)) (.leaf (⟨1,-2,1,-1⟩)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (⟨-2,-3,-1,-2⟩)) (.leaf (⟨-3,-2,-1,-1⟩))) (.branch 19 (.leaf (⟨4,-1,1,0⟩)) (.leaf (⟨-3,-1,-2,-1⟩)))) (.branch 22 (.branch 21 (.leaf (⟨-2,3,-1,1⟩)) (.leaf (⟨3,5,1,2⟩))) (.branch 23 (.leaf (⟨4,3,1,1⟩)) (.leaf (⟨-1,3,-1,2⟩))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (⟨5,-3,2,-1⟩)) (.leaf (⟨-3,-8,-1,-3⟩))) (.branch 27 (.leaf (⟨3,-4,1,-1⟩)) (.leaf (⟨-4,-7,-1,-2⟩)))) (.branch 30 (.branch 29 (.leaf (⟨5,2,2,1⟩)) (.leaf (⟨-8,3,-3,1⟩))) (.branch 31 (.leaf (⟨-7,-3,-2,-1⟩)) (.leaf (⟨-8,-5,-3,-2⟩)))))))
noncomputable def liftMatrix (p : Fin 32) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 32) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],6⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],7⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],10⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],11⟩,⟨⟨1,4,0,1⟩,[.t (4)],12⟩,⟨⟨-1,-5,0,-1⟩,[.t (5)],13⟩,⟨⟨-5,-4,-1,-1⟩,[.t (5),.s,.t (1)],14⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],15⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],16⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],17⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],18⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],19⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],20⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],21⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],22⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],23⟩,⟨⟨5,-3,2,-1⟩,[.t (2),.s,.t (-2),.s,.t (-1)],24⟩,⟨⟨-3,-8,-1,-3⟩,[.t (3),.s,.t (3)],25⟩,⟨⟨3,-4,1,-1⟩,[.t (3),.s,.t (-1)],26⟩,⟨⟨-4,-7,-1,-2⟩,[.t (4),.s,.t (2)],27⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],28⟩,⟨⟨-8,3,-3,1⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],29⟩,⟨⟨-7,-3,-2,-1⟩,[.t (3),.s,.t (-2),.s,.t (0)],30⟩,⟨⟨-8,-5,-3,-2⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (0)],31⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 32 ∧ ((List.finRange 32).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 32) := [⟨9,2,⟨⟨-1,-6,0,-1⟩,[.t (6)],0⟩⟩,⟨3,1,⟨⟨-1,0,-2,-1⟩,[.t (0),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨6,1,⟨⟨-1,0,2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨23,-3,⟨⟨10,-13,7,-9⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨16,3,⟨⟨-13,22,-3,5⟩,[.t (4),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨28,4,⟨⟨15,-34,4,-9⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨31,5,⟨⟨-27,71,-8,21⟩,[.t (3),.s,.t (-3),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨29,-3,⟨⟨36,-97,13,-35⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨30,5,⟨⟨21,-71,8,-27⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨27,4,⟨⟨-9,34,-4,15⟩,[.t (2),.s,.t (-4),.s,.t (-4)],0⟩⟩,⟨14,3,⟨⟨5,-22,3,-13⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨13,2,⟨⟨-1,6,0,-1⟩,[.t (-6)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(0,1),(1,1),(3,2),(2,1),(5,2),(8,3),(3,1),(7,2),(4,1),(5,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end PSL2_13_c1

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
