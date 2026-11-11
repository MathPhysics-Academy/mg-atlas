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
namespace G120_5_c2
noncomputable def originalSData : LookupTree (Fin 40) :=
  (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (6)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (9)) (.leaf (3))) (.branch 8 (.leaf (12)) (.branch 9 (.leaf (13)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (16)) (.leaf (17))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (15))))) (.branch 17 (.branch 16 (.leaf (14)) (.leaf (10))) (.branch 18 (.leaf (11)) (.branch 19 (.leaf (21)) (.leaf (23))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (25)) (.leaf (18))) (.branch 23 (.leaf (27)) (.branch 24 (.leaf (19)) (.leaf (29))))) (.branch 27 (.branch 26 (.leaf (20)) (.leaf (30))) (.branch 28 (.leaf (22)) (.branch 29 (.leaf (33)) (.leaf (24)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (26)) (.leaf (32))) (.branch 33 (.leaf (31)) (.branch 34 (.leaf (28)) (.leaf (37))))) (.branch 37 (.branch 36 (.leaf (38)) (.leaf (39))) (.branch 38 (.leaf (34)) (.branch 39 (.leaf (35)) (.leaf (36))))))))
noncomputable def originalS (p : Fin 40) : Fin 40 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 40) :=
  (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (7)) (.leaf (8))))) (.branch 7 (.branch 6 (.leaf (10)) (.leaf (11))) (.branch 8 (.leaf (13)) (.branch 9 (.leaf (14)) (.leaf (15)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (17)) (.leaf (18))) (.branch 13 (.leaf (19)) (.branch 14 (.leaf (1)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (12)) (.leaf (20))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (22)) (.leaf (24))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (26)) (.leaf (16))) (.branch 23 (.leaf (28)) (.branch 24 (.leaf (6)) (.leaf (29))))) (.branch 27 (.branch 26 (.leaf (9)) (.leaf (31))) (.branch 28 (.leaf (32)) (.branch 29 (.leaf (23)) (.leaf (33)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (34)) (.leaf (21))) (.branch 33 (.leaf (35)) (.branch 34 (.leaf (36)) (.leaf (38))))) (.branch 37 (.branch 36 (.leaf (39)) (.leaf (37))) (.branch 38 (.leaf (25)) (.branch 39 (.leaf (30)) (.leaf (27))))))))
noncomputable def originalT (p : Fin 40) : Fin 40 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 40) :=
  (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (6))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (8)) (.leaf (9)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (10)) (.leaf (11))) (.branch 13 (.leaf (12)) (.branch 14 (.leaf (13)) (.leaf (14))))) (.branch 17 (.branch 16 (.leaf (15)) (.leaf (16))) (.branch 18 (.leaf (17)) (.branch 19 (.leaf (18)) (.leaf (19))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (20)) (.leaf (21))) (.branch 23 (.leaf (22)) (.branch 24 (.leaf (23)) (.leaf (24))))) (.branch 27 (.branch 26 (.leaf (25)) (.leaf (26))) (.branch 28 (.leaf (27)) (.branch 29 (.leaf (28)) (.leaf (29)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (30)) (.leaf (31))) (.branch 33 (.leaf (32)) (.branch 34 (.leaf (33)) (.leaf (34))))) (.branch 37 (.branch 36 (.leaf (35)) (.leaf (36))) (.branch 38 (.leaf (37)) (.branch 39 (.leaf (38)) (.leaf (39))))))))
noncomputable def projection (p : Fin 40) : Fin 40 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 40) :=
  (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (3)) (.leaf (4))))) (.branch 7 (.branch 6 (.leaf (5)) (.leaf (6))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (8)) (.leaf (9)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (10)) (.leaf (11))) (.branch 13 (.leaf (12)) (.branch 14 (.leaf (13)) (.leaf (14))))) (.branch 17 (.branch 16 (.leaf (15)) (.leaf (16))) (.branch 18 (.leaf (17)) (.branch 19 (.leaf (18)) (.leaf (19))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (20)) (.leaf (21))) (.branch 23 (.leaf (22)) (.branch 24 (.leaf (23)) (.leaf (24))))) (.branch 27 (.branch 26 (.leaf (25)) (.leaf (26))) (.branch 28 (.leaf (27)) (.branch 29 (.leaf (28)) (.leaf (29)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (30)) (.leaf (31))) (.branch 33 (.leaf (32)) (.branch 34 (.leaf (33)) (.leaf (34))))) (.branch 37 (.branch 36 (.leaf (35)) (.leaf (36))) (.branch 38 (.leaf (37)) (.branch 39 (.leaf (38)) (.leaf (39))))))))
noncomputable def representative (p : Fin 40) : Fin 40 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 40) :=
  (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (6)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (9)) (.leaf (3))) (.branch 8 (.leaf (12)) (.branch 9 (.leaf (13)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (16)) (.leaf (17))) (.branch 13 (.leaf (7)) (.branch 14 (.leaf (8)) (.leaf (15))))) (.branch 17 (.branch 16 (.leaf (14)) (.leaf (10))) (.branch 18 (.leaf (11)) (.branch 19 (.leaf (21)) (.leaf (23))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (25)) (.leaf (18))) (.branch 23 (.leaf (27)) (.branch 24 (.leaf (19)) (.leaf (29))))) (.branch 27 (.branch 26 (.leaf (20)) (.leaf (30))) (.branch 28 (.leaf (22)) (.branch 29 (.leaf (33)) (.leaf (24)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (26)) (.leaf (32))) (.branch 33 (.leaf (31)) (.branch 34 (.leaf (28)) (.leaf (37))))) (.branch 37 (.branch 36 (.leaf (38)) (.leaf (39))) (.branch 38 (.leaf (34)) (.branch 39 (.leaf (35)) (.leaf (36))))))))
noncomputable def S (p : Fin 40) : Fin 40 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 40) :=
  (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (7)) (.leaf (8))))) (.branch 7 (.branch 6 (.leaf (10)) (.leaf (11))) (.branch 8 (.leaf (13)) (.branch 9 (.leaf (14)) (.leaf (15)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (17)) (.leaf (18))) (.branch 13 (.leaf (19)) (.branch 14 (.leaf (1)) (.leaf (4))))) (.branch 17 (.branch 16 (.leaf (12)) (.leaf (20))) (.branch 18 (.leaf (0)) (.branch 19 (.leaf (22)) (.leaf (24))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (26)) (.leaf (16))) (.branch 23 (.leaf (28)) (.branch 24 (.leaf (6)) (.leaf (29))))) (.branch 27 (.branch 26 (.leaf (9)) (.leaf (31))) (.branch 28 (.leaf (32)) (.branch 29 (.leaf (23)) (.leaf (33)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (34)) (.leaf (21))) (.branch 33 (.leaf (35)) (.branch 34 (.leaf (36)) (.leaf (38))))) (.branch 37 (.branch 36 (.leaf (39)) (.leaf (37))) (.branch 38 (.leaf (25)) (.branch 39 (.leaf (30)) (.leaf (27))))))))
noncomputable def T (p : Fin 40) : Fin 40 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 40) :=
  (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (17)) (.leaf (13))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (14))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (23))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (25)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (5)) (.leaf (6))) (.branch 13 (.leaf (15)) (.branch 14 (.leaf (7)) (.leaf (8))))) (.branch 17 (.branch 16 (.leaf (9)) (.leaf (21))) (.branch 18 (.leaf (10)) (.branch 19 (.leaf (11)) (.leaf (12))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (16)) (.leaf (31))) (.branch 23 (.leaf (18)) (.branch 24 (.leaf (28)) (.leaf (19))))) (.branch 27 (.branch 26 (.leaf (37)) (.leaf (20))) (.branch 28 (.leaf (39)) (.branch 29 (.leaf (22)) (.leaf (24)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (38)) (.leaf (26))) (.branch 33 (.leaf (27)) (.branch 34 (.leaf (29)) (.leaf (30))))) (.branch 37 (.branch 36 (.leaf (32)) (.leaf (33))) (.branch 38 (.leaf (36)) (.branch 39 (.leaf (34)) (.leaf (35))))))))
noncomputable def Ti (p : Fin 40) : Fin 40 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 40) : Fin 40 := T (S p)
theorem quotient_relations : (∀ p : Fin 40, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 40, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 40, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 40, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 40)) := [[0,3,11],[1,2,8],[4,5,15],[6,7,19],[9,10,20],[12,13,14],[16,17,18],[21,22,32],[23,24,33],[25,26,34],[27,28,36],[29],[30,31,35],[37,38,39]]
noncomputable def verticesIndexData : LookupTree (Fin 40) :=
 (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (1)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (9))) (.branch 8 (.leaf (10)) (.branch 9 (.leaf (5)) (.leaf (12)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (13)) (.leaf (2))) (.branch 13 (.leaf (15)) (.branch 14 (.leaf (16)) (.leaf (17))))) (.branch 17 (.branch 16 (.leaf (8)) (.leaf (18))) (.branch 18 (.leaf (19)) (.branch 19 (.leaf (20)) (.leaf (11))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (14)) (.leaf (21))) (.branch 23 (.leaf (22)) (.branch 24 (.leaf (24)) (.leaf (25))))) (.branch 27 (.branch 26 (.leaf (27)) (.leaf (28))) (.branch 28 (.leaf (30)) (.branch 29 (.leaf (31)) (.leaf (33)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (34)) (.leaf (35))) (.branch 33 (.leaf (23)) (.branch 34 (.leaf (26)) (.leaf (29))))) (.branch 37 (.branch 36 (.leaf (36)) (.leaf (32))) (.branch 38 (.leaf (37)) (.branch 39 (.leaf (38)) (.leaf (39))))))))
noncomputable def verticesIndex (p : Fin 40) : Fin 40 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 40) :=
 (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (11)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (8)) (.leaf (4))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (15)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (19))) (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (20))))) (.branch 17 (.branch 16 (.leaf (12)) (.leaf (13))) (.branch 18 (.leaf (14)) (.branch 19 (.leaf (16)) (.leaf (17))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (18)) (.leaf (21))) (.branch 23 (.leaf (22)) (.branch 24 (.leaf (32)) (.leaf (23))))) (.branch 27 (.branch 26 (.leaf (24)) (.leaf (33))) (.branch 28 (.leaf (25)) (.branch 29 (.leaf (26)) (.leaf (34)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (27)) (.leaf (28))) (.branch 33 (.leaf (36)) (.branch 34 (.leaf (29)) (.leaf (30))))) (.branch 37 (.branch 36 (.leaf (31)) (.leaf (35))) (.branch 38 (.leaf (37)) (.branch 39 (.leaf (38)) (.leaf (39))))))))
noncomputable def verticesBack (p : Fin 40) : Fin 40 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 40, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 40 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 40, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 40)) := [[0,1],[2,4],[3,6],[5,9],[7,12],[8,13],[10,16],[11,17],[14,15],[18,21],[19,23],[20,25],[22,27],[24,29],[26,30],[28,33],[31,32],[34,37],[35,38],[36,39]]
noncomputable def edgesIndexData : LookupTree (Fin 40) :=
 (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (5))) (.branch 8 (.leaf (8)) (.branch 9 (.leaf (10)) (.leaf (7)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (12)) (.leaf (14))) (.branch 13 (.leaf (9)) (.branch 14 (.leaf (11)) (.leaf (16))))) (.branch 17 (.branch 16 (.leaf (17)) (.leaf (13))) (.branch 18 (.leaf (15)) (.branch 19 (.leaf (18)) (.leaf (20))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (22)) (.leaf (19))) (.branch 23 (.leaf (24)) (.branch 24 (.leaf (21)) (.leaf (26))))) (.branch 27 (.branch 26 (.leaf (23)) (.leaf (28))) (.branch 28 (.leaf (25)) (.branch 29 (.leaf (30)) (.leaf (27)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (29)) (.leaf (32))) (.branch 33 (.leaf (33)) (.branch 34 (.leaf (31)) (.leaf (34))))) (.branch 37 (.branch 36 (.leaf (36)) (.leaf (38))) (.branch 38 (.leaf (35)) (.branch 39 (.leaf (37)) (.leaf (39))))))))
noncomputable def edgesIndex (p : Fin 40) : Fin 40 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 40) :=
 (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (5))) (.branch 8 (.leaf (9)) (.branch 9 (.leaf (7)) (.leaf (12)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (8)) (.leaf (13))) (.branch 13 (.leaf (10)) (.branch 14 (.leaf (16)) (.leaf (11))))) (.branch 17 (.branch 16 (.leaf (17)) (.leaf (14))) (.branch 18 (.leaf (15)) (.branch 19 (.leaf (18)) (.leaf (21))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (19)) (.leaf (23))) (.branch 23 (.leaf (20)) (.branch 24 (.leaf (25)) (.leaf (22))))) (.branch 27 (.branch 26 (.leaf (27)) (.leaf (24))) (.branch 28 (.leaf (29)) (.branch 29 (.leaf (26)) (.leaf (30)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (28)) (.leaf (33))) (.branch 33 (.leaf (31)) (.branch 34 (.leaf (32)) (.leaf (34))))) (.branch 37 (.branch 36 (.leaf (37)) (.leaf (35))) (.branch 38 (.leaf (38)) (.branch 39 (.leaf (36)) (.leaf (39))))))))
noncomputable def edgesBack (p : Fin 40) : Fin 40 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 40, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 40 := by decide +kernel
theorem edges_partition : ∀ p : Fin 40, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 40)) := [[0,2,5,10,17],[1,3,7,13],[4,8,14],[6,11,18,22,28,23],[9,15,12,19,24,29,33,36,37,25],[16,20,26,31,21],[27,32,35,39],[30,34,38]]
noncomputable def facesIndexData : LookupTree (Fin 40) :=
 (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (5))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (6)) (.leaf (9))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (12))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (10)) (.leaf (18)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (3)) (.leaf (13))) (.branch 13 (.leaf (20)) (.branch 14 (.leaf (8)) (.leaf (11))))) (.branch 17 (.branch 16 (.leaf (19)) (.leaf (28))) (.branch 18 (.leaf (4)) (.branch 19 (.leaf (14)) (.leaf (21))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (29)) (.leaf (32))) (.branch 23 (.leaf (15)) (.branch 24 (.leaf (17)) (.leaf (22))))) (.branch 27 (.branch 26 (.leaf (27)) (.leaf (30))) (.branch 28 (.leaf (33)) (.branch 29 (.leaf (16)) (.leaf (23)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (37)) (.leaf (31))) (.branch 33 (.leaf (34)) (.branch 34 (.leaf (24)) (.leaf (38))))) (.branch 37 (.branch 36 (.leaf (35)) (.leaf (25))) (.branch 38 (.leaf (26)) (.branch 39 (.leaf (39)) (.leaf (36))))))))
noncomputable def facesIndex (p : Fin 40) : Fin 40 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 40) :=
 (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (10)) (.leaf (17))))) (.branch 7 (.branch 6 (.leaf (1)) (.leaf (3))) (.branch 8 (.leaf (7)) (.branch 9 (.leaf (13)) (.leaf (4)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (8)) (.leaf (14))) (.branch 13 (.leaf (6)) (.branch 14 (.leaf (11)) (.leaf (18))))) (.branch 17 (.branch 16 (.leaf (22)) (.leaf (28))) (.branch 18 (.leaf (23)) (.branch 19 (.leaf (9)) (.leaf (15))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (12)) (.leaf (19))) (.branch 23 (.leaf (24)) (.branch 24 (.leaf (29)) (.leaf (33))))) (.branch 27 (.branch 26 (.leaf (36)) (.leaf (37))) (.branch 28 (.leaf (25)) (.branch 29 (.leaf (16)) (.leaf (20)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (26)) (.leaf (31))) (.branch 33 (.leaf (21)) (.branch 34 (.leaf (27)) (.leaf (32))))) (.branch 37 (.branch 36 (.leaf (35)) (.leaf (39))) (.branch 38 (.leaf (30)) (.branch 39 (.leaf (34)) (.leaf (38))))))))
noncomputable def facesBack (p : Fin 40) : Fin 40 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 40, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 40 := by decide +kernel
theorem faces_partition : ∀ p : Fin 40, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [5,4,3,6,10,5,4,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 14 - 20 + 8 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 1 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 20 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.leaf (⟨-1,1,-1,0⟩))))) (.branch 7 (.branch 6 (.leaf (⟨1,2,0,1⟩)) (.leaf (⟨-1,0,1,-1⟩))) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.branch 9 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨2,-1,1,0⟩)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (⟨-1,-3,0,-1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 13 (.leaf (⟨1,0,2,1⟩)) (.branch 14 (.leaf (⟨0,1,-1,1⟩)) (.leaf (⟨1,1,1,2⟩))))) (.branch 17 (.branch 16 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨-3,1,-1,0⟩))) (.branch 18 (.leaf (⟨1,4,0,1⟩)) (.branch 19 (.leaf (⟨4,3,1,1⟩)) (.leaf (⟨1,1,-2,-1⟩))))))) (.branch 30 (.branch 25 (.branch 22 (.branch 21 (.leaf (⟨-3,-2,-1,-1⟩)) (.leaf (⟨3,-4,1,-1⟩))) (.branch 23 (.leaf (⟨-4,-7,-1,-2⟩)) (.branch 24 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-2,2,3⟩))))) (.branch 27 (.branch 26 (.leaf (⟨-2,3,-1,1⟩)) (.leaf (⟨3,5,1,2⟩))) (.branch 28 (.leaf (⟨-7,4,-2,1⟩)) (.branch 29 (.leaf (⟨4,11,1,3⟩)) (.leaf (⟨-2,1,3,-2⟩)))))) (.branch 35 (.branch 32 (.branch 31 (.leaf (⟨5,-3,2,-1⟩)) (.leaf (⟨-3,-8,-1,-3⟩))) (.branch 33 (.leaf (⟨-7,-3,-2,-1⟩)) (.branch 34 (.leaf (⟨-2,-1,3,1⟩)) (.leaf (⟨5,2,2,1⟩))))) (.branch 37 (.branch 36 (.leaf (⟨-8,-5,-3,-2⟩)) (.leaf (⟨11,7,3,2⟩))) (.branch 38 (.leaf (⟨2,-5,1,-2⟩)) (.branch 39 (.leaf (⟨-5,-7,-2,-3⟩)) (.leaf (⟨-7,-2,-3,-1⟩))))))))
noncomputable def liftMatrix (p : Fin 40) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 40) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],13⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],14⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],15⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],16⟩,⟨⟨1,4,0,1⟩,[.t (4)],17⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],18⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],19⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],20⟩,⟨⟨3,-4,1,-1⟩,[.t (3),.s,.t (-1)],21⟩,⟨⟨-4,-7,-1,-2⟩,[.t (4),.s,.t (2)],22⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],23⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],24⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],25⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],26⟩,⟨⟨-7,4,-2,1⟩,[.t (3),.s,.t (-2),.s,.t (-1)],27⟩,⟨⟨4,11,1,3⟩,[.t (4),.s,.t (3)],28⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],29⟩,⟨⟨5,-3,2,-1⟩,[.t (2),.s,.t (-2),.s,.t (-1)],30⟩,⟨⟨-3,-8,-1,-3⟩,[.t (3),.s,.t (3)],31⟩,⟨⟨-7,-3,-2,-1⟩,[.t (3),.s,.t (-2),.s,.t (0)],32⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],33⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],34⟩,⟨⟨-8,-5,-3,-2⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (0)],35⟩,⟨⟨11,7,3,2⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (0)],36⟩,⟨⟨2,-5,1,-2⟩,[.t (2),.s,.t (-2)],37⟩,⟨⟨-5,-7,-2,-3⟩,[.t (2),.s,.t (-2),.s,.t (1)],38⟩,⟨⟨-7,-2,-3,-1⟩,[.t (2),.s,.t (-3),.s,.t (0)],39⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 40 ∧ ((List.finRange 40).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 40) := [⟨11,2,⟨⟨1,5,0,1⟩,[.t (5)],0⟩⟩,⟨33,4,⟨⟨-23,-19,-6,-5⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨29,-3,⟨⟨-11,-7,19,12⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,1,⟨⟨-1,0,-4,-1⟩,[.t (0),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨12,1,⟨⟨-1,0,4,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨14,3,⟨⟨4,-3,3,-2⟩,[.t (1),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨15,3,⟨⟨-2,3,-3,4⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨39,7,⟨⟨40,-91,11,-25⟩,[.t (3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨38,6,⟨⟨-31,75,-12,29⟩,[.t (2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨35,6,⟨⟨29,-75,12,-31⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨31,5,⟨⟨16,-45,5,-14⟩,[.t (3),.s,.t (-5),.s,.t (-3)],0⟩⟩,⟨32,5,⟨⟨-14,45,-5,16⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨36,7,⟨⟨-25,91,-11,40⟩,[.t (2),.s,.t (-4),.s,.t (-3),.s,.t (-4)],0⟩⟩,⟨28,4,⟨⟨-5,19,6,-23⟩,[.t (-1),.s,.t (-6),.s,.t (-4)],0⟩⟩,⟨17,2,⟨⟨1,-5,0,1⟩,[.t (-5)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-2,3),(-1,2),(0,1),(1,2),(1,1),(2,1),(7,3),(5,2),(8,3),(3,1),(7,2),(11,3),(4,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G120_5_c2

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
