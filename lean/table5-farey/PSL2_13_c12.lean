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
namespace PSL2_13_c12
noncomputable def originalSData : LookupTree (Fin 52) :=
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (14))) (.branch 12 (.leaf (16)) (.leaf (18)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (20)) (.branch 15 (.leaf (10)) (.leaf (23)))) (.branch 17 (.leaf (11)) (.branch 18 (.leaf (24)) (.leaf (12))))) (.branch 22 (.branch 20 (.leaf (26)) (.branch 21 (.leaf (13)) (.leaf (28)))) (.branch 24 (.branch 23 (.leaf (30)) (.leaf (15))) (.branch 25 (.leaf (17)) (.leaf (31))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (19)) (.branch 28 (.leaf (33)) (.leaf (21)))) (.branch 30 (.leaf (35)) (.branch 31 (.leaf (22)) (.leaf (25))))) (.branch 35 (.branch 33 (.leaf (36)) (.branch 34 (.leaf (27)) (.leaf (37)))) (.branch 37 (.branch 36 (.leaf (29)) (.leaf (32))) (.branch 38 (.leaf (34)) (.leaf (42)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (41)) (.branch 41 (.leaf (44)) (.leaf (39)))) (.branch 43 (.leaf (38)) (.branch 44 (.leaf (45)) (.leaf (40))))) (.branch 48 (.branch 46 (.leaf (43)) (.branch 47 (.leaf (48)) (.leaf (49)))) (.branch 50 (.branch 49 (.leaf (46)) (.leaf (47))) (.branch 51 (.leaf (51)) (.leaf (50))))))))
noncomputable def originalS (p : Fin 52) : Fin 52 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 52) :=
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (8)) (.leaf (10))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (1)) (.leaf (12)))) (.branch 11 (.branch 10 (.leaf (13)) (.leaf (15))) (.branch 12 (.leaf (17)) (.leaf (19)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (21)) (.branch 15 (.leaf (22)) (.leaf (16)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (25)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (27)) (.branch 21 (.leaf (4)) (.leaf (29)))) (.branch 24 (.branch 23 (.leaf (14)) (.leaf (30))) (.branch 25 (.leaf (23)) (.leaf (32))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (33)) (.branch 28 (.leaf (18)) (.leaf (34)))) (.branch 30 (.leaf (24)) (.branch 31 (.leaf (9)) (.leaf (35))))) (.branch 35 (.branch 33 (.leaf (37)) (.branch 34 (.leaf (38)) (.leaf (39)))) (.branch 37 (.branch 36 (.leaf (40)) (.leaf (41))) (.branch 38 (.leaf (20)) (.leaf (43)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (31)) (.branch 41 (.leaf (44)) (.leaf (36)))) (.branch 43 (.leaf (26)) (.branch 44 (.leaf (46)) (.leaf (28))))) (.branch 48 (.branch 46 (.leaf (47)) (.branch 47 (.leaf (49)) (.leaf (50)))) (.branch 50 (.branch 49 (.leaf (51)) (.leaf (42))) (.branch 51 (.leaf (45)) (.leaf (48))))))))
noncomputable def originalT (p : Fin 52) : Fin 52 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 52) :=
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (8)))) (.branch 11 (.branch 10 (.leaf (9)) (.leaf (10))) (.branch 12 (.leaf (11)) (.leaf (12)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (13)) (.branch 15 (.leaf (14)) (.leaf (15)))) (.branch 17 (.leaf (16)) (.branch 18 (.leaf (17)) (.leaf (18))))) (.branch 22 (.branch 20 (.leaf (19)) (.branch 21 (.leaf (20)) (.leaf (21)))) (.branch 24 (.branch 23 (.leaf (22)) (.leaf (23))) (.branch 25 (.leaf (24)) (.leaf (25))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (26)) (.branch 28 (.leaf (27)) (.leaf (28)))) (.branch 30 (.leaf (29)) (.branch 31 (.leaf (30)) (.leaf (31))))) (.branch 35 (.branch 33 (.leaf (32)) (.branch 34 (.leaf (33)) (.leaf (34)))) (.branch 37 (.branch 36 (.leaf (35)) (.leaf (36))) (.branch 38 (.leaf (37)) (.leaf (38)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (39)) (.branch 41 (.leaf (40)) (.leaf (41)))) (.branch 43 (.leaf (42)) (.branch 44 (.leaf (43)) (.leaf (44))))) (.branch 48 (.branch 46 (.leaf (45)) (.branch 47 (.leaf (46)) (.leaf (47)))) (.branch 50 (.branch 49 (.leaf (48)) (.leaf (49))) (.branch 51 (.leaf (50)) (.leaf (51))))))))
noncomputable def projection (p : Fin 52) : Fin 52 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 52) :=
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (8)))) (.branch 11 (.branch 10 (.leaf (9)) (.leaf (10))) (.branch 12 (.leaf (11)) (.leaf (12)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (13)) (.branch 15 (.leaf (14)) (.leaf (15)))) (.branch 17 (.leaf (16)) (.branch 18 (.leaf (17)) (.leaf (18))))) (.branch 22 (.branch 20 (.leaf (19)) (.branch 21 (.leaf (20)) (.leaf (21)))) (.branch 24 (.branch 23 (.leaf (22)) (.leaf (23))) (.branch 25 (.leaf (24)) (.leaf (25))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (26)) (.branch 28 (.leaf (27)) (.leaf (28)))) (.branch 30 (.leaf (29)) (.branch 31 (.leaf (30)) (.leaf (31))))) (.branch 35 (.branch 33 (.leaf (32)) (.branch 34 (.leaf (33)) (.leaf (34)))) (.branch 37 (.branch 36 (.leaf (35)) (.leaf (36))) (.branch 38 (.leaf (37)) (.leaf (38)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (39)) (.branch 41 (.leaf (40)) (.leaf (41)))) (.branch 43 (.leaf (42)) (.branch 44 (.leaf (43)) (.leaf (44))))) (.branch 48 (.branch 46 (.leaf (45)) (.branch 47 (.leaf (46)) (.leaf (47)))) (.branch 50 (.branch 49 (.leaf (48)) (.leaf (49))) (.branch 51 (.leaf (50)) (.leaf (51))))))))
noncomputable def representative (p : Fin 52) : Fin 52 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 52) :=
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (5)) (.leaf (14))) (.branch 12 (.leaf (16)) (.leaf (18)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (20)) (.branch 15 (.leaf (10)) (.leaf (23)))) (.branch 17 (.leaf (11)) (.branch 18 (.leaf (24)) (.leaf (12))))) (.branch 22 (.branch 20 (.leaf (26)) (.branch 21 (.leaf (13)) (.leaf (28)))) (.branch 24 (.branch 23 (.leaf (30)) (.leaf (15))) (.branch 25 (.leaf (17)) (.leaf (31))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (19)) (.branch 28 (.leaf (33)) (.leaf (21)))) (.branch 30 (.leaf (35)) (.branch 31 (.leaf (22)) (.leaf (25))))) (.branch 35 (.branch 33 (.leaf (36)) (.branch 34 (.leaf (27)) (.leaf (37)))) (.branch 37 (.branch 36 (.leaf (29)) (.leaf (32))) (.branch 38 (.leaf (34)) (.leaf (42)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (41)) (.branch 41 (.leaf (44)) (.leaf (39)))) (.branch 43 (.leaf (38)) (.branch 44 (.leaf (45)) (.leaf (40))))) (.branch 48 (.branch 46 (.leaf (43)) (.branch 47 (.leaf (48)) (.leaf (49)))) (.branch 50 (.branch 49 (.leaf (46)) (.leaf (47))) (.branch 51 (.leaf (51)) (.leaf (50))))))))
noncomputable def S (p : Fin 52) : Fin 52 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 52) :=
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (8)) (.leaf (10))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (1)) (.leaf (12)))) (.branch 11 (.branch 10 (.leaf (13)) (.leaf (15))) (.branch 12 (.leaf (17)) (.leaf (19)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (21)) (.branch 15 (.leaf (22)) (.leaf (16)))) (.branch 17 (.leaf (0)) (.branch 18 (.leaf (25)) (.leaf (6))))) (.branch 22 (.branch 20 (.leaf (27)) (.branch 21 (.leaf (4)) (.leaf (29)))) (.branch 24 (.branch 23 (.leaf (14)) (.leaf (30))) (.branch 25 (.leaf (23)) (.leaf (32))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (33)) (.branch 28 (.leaf (18)) (.leaf (34)))) (.branch 30 (.leaf (24)) (.branch 31 (.leaf (9)) (.leaf (35))))) (.branch 35 (.branch 33 (.leaf (37)) (.branch 34 (.leaf (38)) (.leaf (39)))) (.branch 37 (.branch 36 (.leaf (40)) (.leaf (41))) (.branch 38 (.leaf (20)) (.leaf (43)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (31)) (.branch 41 (.leaf (44)) (.leaf (36)))) (.branch 43 (.leaf (26)) (.branch 44 (.leaf (46)) (.leaf (28))))) (.branch 48 (.branch 46 (.leaf (47)) (.branch 47 (.leaf (49)) (.leaf (50)))) (.branch 50 (.branch 49 (.leaf (51)) (.leaf (42))) (.branch 51 (.leaf (45)) (.leaf (48))))))))
noncomputable def T (p : Fin 52) : Fin 52 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 52) :=
  (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (16)) (.branch 2 (.leaf (7)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (20)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (18)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 11 (.branch 10 (.leaf (30)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (8)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (9)) (.branch 15 (.leaf (22)) (.leaf (10)))) (.branch 17 (.leaf (15)) (.branch 18 (.leaf (11)) (.leaf (27))))) (.branch 22 (.branch 20 (.leaf (12)) (.branch 21 (.leaf (37)) (.leaf (13)))) (.branch 24 (.branch 23 (.leaf (14)) (.leaf (24))) (.branch 25 (.leaf (29)) (.leaf (17))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (42)) (.branch 28 (.leaf (19)) (.leaf (44)))) (.branch 30 (.leaf (21)) (.branch 31 (.leaf (23)) (.leaf (39))))) (.branch 35 (.branch 33 (.leaf (25)) (.branch 34 (.leaf (26)) (.leaf (28)))) (.branch 37 (.branch 36 (.leaf (31)) (.leaf (41))) (.branch 38 (.leaf (32)) (.leaf (33)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (34)) (.branch 41 (.leaf (35)) (.leaf (36)))) (.branch 43 (.leaf (49)) (.branch 44 (.leaf (38)) (.leaf (40))))) (.branch 48 (.branch 46 (.leaf (50)) (.branch 47 (.leaf (43)) (.leaf (45)))) (.branch 50 (.branch 49 (.leaf (51)) (.leaf (46))) (.branch 51 (.leaf (47)) (.leaf (48))))))))
noncomputable def Ti (p : Fin 52) : Fin 52 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 52) : Fin 52 := T (S p)
theorem quotient_relations : (∀ p : Fin 52, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 52, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 52, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 52, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 52)) := [[0,3,11],[1,2,8],[4,5,13],[6,7,12],[9,10,22],[14,15,30],[16,17,23],[18,19,33],[20,21,34],[24,25,35],[26,27,38],[28,29,40],[31,32,41],[36,37,39],[42,43,47],[44],[45,46,51],[48,49,50]]
noncomputable def verticesIndexData : LookupTree (Fin 52) :=
 (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))) (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (2)) (.leaf (11)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (8)) (.branch 15 (.leaf (15)) (.leaf (16)))) (.branch 17 (.leaf (18)) (.branch 18 (.leaf (19)) (.leaf (21))))) (.branch 22 (.branch 20 (.leaf (22)) (.branch 21 (.leaf (24)) (.leaf (25)))) (.branch 24 (.branch 23 (.leaf (14)) (.leaf (20))) (.branch 25 (.leaf (27)) (.leaf (28))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (30)) (.branch 28 (.leaf (31)) (.leaf (33)))) (.branch 30 (.leaf (34)) (.branch 31 (.leaf (17)) (.leaf (36))))) (.branch 35 (.branch 33 (.leaf (37)) (.branch 34 (.leaf (23)) (.leaf (26)))) (.branch 37 (.branch 36 (.leaf (29)) (.leaf (39))) (.branch 38 (.leaf (40)) (.leaf (32)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (41)) (.branch 41 (.leaf (35)) (.leaf (38)))) (.branch 43 (.leaf (42)) (.branch 44 (.leaf (43)) (.leaf (45))))) (.branch 48 (.branch 46 (.leaf (46)) (.branch 47 (.leaf (47)) (.leaf (44)))) (.branch 50 (.branch 49 (.leaf (49)) (.leaf (50))) (.branch 51 (.leaf (51)) (.leaf (48))))))))
noncomputable def verticesIndex (p : Fin 52) : Fin 52 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 52) :=
 (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (11)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (13)))) (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (12)) (.leaf (9)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (10)) (.branch 15 (.leaf (22)) (.leaf (14)))) (.branch 17 (.leaf (15)) (.branch 18 (.leaf (30)) (.leaf (16))))) (.branch 22 (.branch 20 (.leaf (17)) (.branch 21 (.leaf (23)) (.leaf (18)))) (.branch 24 (.branch 23 (.leaf (19)) (.leaf (33))) (.branch 25 (.leaf (20)) (.leaf (21))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (34)) (.branch 28 (.leaf (24)) (.leaf (25)))) (.branch 30 (.leaf (35)) (.branch 31 (.leaf (26)) (.leaf (27))))) (.branch 35 (.branch 33 (.leaf (38)) (.branch 34 (.leaf (28)) (.leaf (29)))) (.branch 37 (.branch 36 (.leaf (40)) (.leaf (31))) (.branch 38 (.leaf (32)) (.leaf (41)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (36)) (.branch 41 (.leaf (37)) (.leaf (39)))) (.branch 43 (.leaf (42)) (.branch 44 (.leaf (43)) (.leaf (47))))) (.branch 48 (.branch 46 (.leaf (44)) (.branch 47 (.leaf (45)) (.leaf (46)))) (.branch 50 (.branch 49 (.leaf (51)) (.leaf (48))) (.branch 51 (.leaf (49)) (.leaf (50))))))))
noncomputable def verticesBack (p : Fin 52) : Fin 52 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 52, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 52 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 52, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 52)) := [[0,1],[2,4],[3,6],[5,9],[7,8],[10,14],[11,16],[12,18],[13,20],[15,23],[17,24],[19,26],[21,28],[22,30],[25,31],[27,33],[29,35],[32,36],[34,37],[38,42],[39,41],[40,44],[43,45],[46,48],[47,49],[50,51]]
noncomputable def edgesIndexData : LookupTree (Fin 52) :=
 (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (9)))) (.branch 11 (.branch 10 (.leaf (7)) (.leaf (10))) (.branch 12 (.leaf (12)) (.leaf (14)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (16)) (.branch 15 (.leaf (11)) (.leaf (18)))) (.branch 17 (.leaf (13)) (.branch 18 (.leaf (20)) (.leaf (15))))) (.branch 22 (.branch 20 (.leaf (22)) (.branch 21 (.leaf (17)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (26)) (.leaf (19))) (.branch 25 (.leaf (21)) (.leaf (28))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (23)) (.branch 28 (.leaf (30)) (.leaf (25)))) (.branch 30 (.leaf (32)) (.branch 31 (.leaf (27)) (.leaf (29))))) (.branch 35 (.branch 33 (.leaf (34)) (.branch 34 (.leaf (31)) (.leaf (36)))) (.branch 37 (.branch 36 (.leaf (33)) (.leaf (35))) (.branch 38 (.leaf (37)) (.leaf (38)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (40)) (.branch 41 (.leaf (42)) (.leaf (41)))) (.branch 43 (.leaf (39)) (.branch 44 (.leaf (44)) (.leaf (43))))) (.branch 48 (.branch 46 (.leaf (45)) (.branch 47 (.leaf (46)) (.leaf (48)))) (.branch 50 (.branch 49 (.leaf (47)) (.leaf (49))) (.branch 51 (.leaf (50)) (.leaf (51))))))))
noncomputable def edgesIndex (p : Fin 52) : Fin 52 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 52) :=
 (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (8)) (.leaf (10))) (.branch 12 (.leaf (14)) (.leaf (11)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (16)) (.branch 15 (.leaf (12)) (.leaf (18)))) (.branch 17 (.leaf (13)) (.branch 18 (.leaf (20)) (.leaf (15))))) (.branch 22 (.branch 20 (.leaf (23)) (.branch 21 (.leaf (17)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (19)) (.leaf (26))) (.branch 25 (.leaf (21)) (.leaf (28))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (22)) (.branch 28 (.leaf (30)) (.leaf (25)))) (.branch 30 (.leaf (31)) (.branch 31 (.leaf (27)) (.leaf (33))))) (.branch 35 (.branch 33 (.leaf (29)) (.branch 34 (.leaf (35)) (.leaf (32)))) (.branch 37 (.branch 36 (.leaf (36)) (.leaf (34))) (.branch 38 (.leaf (37)) (.leaf (38)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (42)) (.branch 41 (.leaf (39)) (.leaf (41)))) (.branch 43 (.leaf (40)) (.branch 44 (.leaf (44)) (.leaf (43))))) (.branch 48 (.branch 46 (.leaf (45)) (.branch 47 (.leaf (46)) (.leaf (48)))) (.branch 50 (.branch 49 (.leaf (47)) (.leaf (49))) (.branch 51 (.leaf (50)) (.leaf (51))))))))
noncomputable def edgesBack (p : Fin 52) : Fin 52 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 52, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 52 := by decide +kernel
theorem edges_partition : ∀ p : Fin 52, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 52)) := [[0,2,5,10,15,16],[1,3,7],[4,8,12,19,27,18,6,11,17,25,32,37,20],[9,13,21,29,24,23,30],[14,22],[26,33,38,43,46,49,42],[28,34,39,31,35,40,44],[36,41],[45,47,50],[48,51]]
noncomputable def facesIndexData : LookupTree (Fin 52) :=
 (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (6)) (.leaf (1)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (9)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (15)) (.branch 8 (.leaf (8)) (.leaf (10)))) (.branch 11 (.branch 10 (.leaf (22)) (.leaf (3))) (.branch 12 (.leaf (16)) (.leaf (11)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (23)) (.branch 15 (.leaf (29)) (.leaf (4)))) (.branch 17 (.leaf (5)) (.branch 18 (.leaf (17)) (.leaf (14))))) (.branch 22 (.branch 20 (.leaf (12)) (.branch 21 (.leaf (21)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (30)) (.leaf (27))) (.branch 25 (.leaf (26)) (.leaf (18))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (31)) (.branch 28 (.leaf (13)) (.leaf (38)))) (.branch 30 (.leaf (25)) (.branch 31 (.leaf (28)) (.leaf (41))))) (.branch 35 (.branch 33 (.leaf (19)) (.branch 34 (.leaf (32)) (.leaf (39)))) (.branch 37 (.branch 36 (.leaf (42)) (.leaf (45))) (.branch 38 (.leaf (20)) (.leaf (33)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (40)) (.branch 41 (.leaf (43)) (.leaf (46)))) (.branch 43 (.leaf (37)) (.branch 44 (.leaf (34)) (.leaf (44))))) (.branch 48 (.branch 46 (.leaf (47)) (.branch 47 (.leaf (35)) (.leaf (48)))) (.branch 50 (.branch 49 (.leaf (50)) (.leaf (36))) (.branch 51 (.leaf (49)) (.leaf (51))))))))
noncomputable def facesIndex (p : Fin 52) : Fin 52 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 52) :=
 (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (10)) (.branch 5 (.leaf (15)) (.leaf (16))))) (.branch 9 (.branch 7 (.leaf (1)) (.branch 8 (.leaf (3)) (.leaf (7)))) (.branch 11 (.branch 10 (.leaf (4)) (.leaf (8))) (.branch 12 (.leaf (12)) (.leaf (19)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (27)) (.branch 15 (.leaf (18)) (.leaf (6)))) (.branch 17 (.leaf (11)) (.branch 18 (.leaf (17)) (.leaf (25))))) (.branch 22 (.branch 20 (.leaf (32)) (.branch 21 (.leaf (37)) (.leaf (20)))) (.branch 24 (.branch 23 (.leaf (9)) (.leaf (13))) (.branch 25 (.leaf (21)) (.leaf (29))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (24)) (.branch 28 (.leaf (23)) (.leaf (30)))) (.branch 30 (.leaf (14)) (.branch 31 (.leaf (22)) (.leaf (26))))) (.branch 35 (.branch 33 (.leaf (33)) (.branch 34 (.leaf (38)) (.leaf (43)))) (.branch 37 (.branch 36 (.leaf (46)) (.leaf (49))) (.branch 38 (.leaf (42)) (.leaf (28)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (34)) (.branch 41 (.leaf (39)) (.leaf (31)))) (.branch 43 (.leaf (35)) (.branch 44 (.leaf (40)) (.leaf (44))))) (.branch 48 (.branch 46 (.leaf (36)) (.branch 47 (.leaf (41)) (.leaf (45)))) (.branch 50 (.branch 49 (.leaf (47)) (.leaf (50))) (.branch 51 (.leaf (48)) (.leaf (51))))))))
noncomputable def facesBack (p : Fin 52) : Fin 52 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 52, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 52 := by decide +kernel
theorem faces_partition : ∀ p : Fin 52, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [6,3,13,7,2,7,7,2,3,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 18 - 26 + 10 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 1 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 26 (.branch 13 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))) (.branch 11 (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.leaf (⟨-1,-3,0,-1⟩))) (.branch 12 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,1,-2,-1⟩)))))) (.branch 19 (.branch 16 (.branch 14 (.leaf (⟨2,1,1,1⟩)) (.branch 15 (.leaf (⟨-3,1,-1,0⟩)) (.leaf (⟨1,4,0,1⟩)))) (.branch 17 (.leaf (⟨-1,-5,0,-1⟩)) (.branch 18 (.leaf (⟨-5,-4,-1,-1⟩)) (.leaf (⟨1,-1,-1,2⟩))))) (.branch 22 (.branch 20 (.leaf (⟨-1,-2,2,3⟩)) (.branch 21 (.leaf (⟨1,-2,1,-1⟩)) (.leaf (⟨-2,-3,-1,-2⟩)))) (.branch 24 (.branch 23 (.leaf (⟨-3,-2,-1,-1⟩)) (.leaf (⟨4,-1,1,0⟩))) (.branch 25 (.leaf (⟨-4,5,-1,1⟩)) (.leaf (⟨5,9,1,2⟩))))))) (.branch 39 (.branch 32 (.branch 29 (.branch 27 (.leaf (⟨-2,1,3,-2⟩)) (.branch 28 (.leaf (⟨1,3,-2,-5⟩)) (.leaf (⟨-3,2,-2,1⟩)))) (.branch 30 (.leaf (⟨2,5,1,3⟩)) (.branch 31 (.leaf (⟨4,3,1,1⟩)) (.leaf (⟨9,-5,2,-1⟩))))) (.branch 35 (.branch 33 (.leaf (⟨-5,-14,-1,-3⟩)) (.branch 34 (.leaf (⟨-2,-1,3,1⟩)) (.leaf (⟨-3,-1,-2,-1⟩)))) (.branch 37 (.branch 36 (.leaf (⟨9,4,2,1⟩)) (.leaf (⟨4,1,3,1⟩))) (.branch 38 (.leaf (⟨-1,3,-1,2⟩)) (.leaf (⟨3,2,-5,-3⟩)))))) (.branch 45 (.branch 42 (.branch 40 (.leaf (⟨3,4,2,3⟩)) (.branch 41 (.leaf (⟨5,3,3,2⟩)) (.leaf (⟨-14,-9,-3,-2⟩)))) (.branch 43 (.leaf (⟨2,-3,-3,5⟩)) (.branch 44 (.leaf (⟨-3,-5,5,8⟩)) (.leaf (⟨3,-5,2,-3⟩))))) (.branch 48 (.branch 46 (.leaf (⟨-5,3,8,-5⟩)) (.branch 47 (.leaf (⟨3,8,-5,-13⟩)) (.leaf (⟨-5,-2,8,3⟩)))) (.branch 50 (.branch 49 (.leaf (⟨7,2,-11,-3⟩)) (.leaf (⟨-2,5,3,-8⟩))) (.branch 51 (.leaf (⟨5,7,-8,-11⟩)) (.leaf (⟨8,5,-13,-8⟩))))))))
noncomputable def liftMatrix (p : Fin 52) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 52) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],13⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],14⟩,⟨⟨1,4,0,1⟩,[.t (4)],15⟩,⟨⟨-1,-5,0,-1⟩,[.t (5)],16⟩,⟨⟨-5,-4,-1,-1⟩,[.t (5),.s,.t (1)],17⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],18⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],19⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],20⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],21⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],22⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],23⟩,⟨⟨-4,5,-1,1⟩,[.t (4),.s,.t (-1)],24⟩,⟨⟨5,9,1,2⟩,[.t (5),.s,.t (2)],25⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],26⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],27⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],28⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],29⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],30⟩,⟨⟨9,-5,2,-1⟩,[.t (4),.s,.t (-2),.s,.t (-1)],31⟩,⟨⟨-5,-14,-1,-3⟩,[.t (5),.s,.t (3)],32⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],33⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],34⟩,⟨⟨9,4,2,1⟩,[.t (4),.s,.t (-2),.s,.t (0)],35⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],36⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],37⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],38⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],39⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],40⟩,⟨⟨-14,-9,-3,-2⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (0)],41⟩,⟨⟨2,-3,-3,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2)],42⟩,⟨⟨-3,-5,5,8⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (1)],43⟩,⟨⟨3,-5,2,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2)],44⟩,⟨⟨-5,3,8,-5⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-1)],45⟩,⟨⟨3,8,-5,-13⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (2)],46⟩,⟨⟨-5,-2,8,3⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (0)],47⟩,⟨⟨7,2,-11,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-4),.s,.t (0)],48⟩,⟨⟨-2,5,3,-8⟩,[.t (-1),.s,.t (-3),.s,.t (-3)],49⟩,⟨⟨5,7,-8,-11⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (1)],50⟩,⟨⟨8,5,-13,-8⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (0)],51⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 52 ∧ ((List.finRange 52).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 52) := [⟨11,2,⟨⟨-1,-6,0,-1⟩,[.t (6)],0⟩⟩,⟨33,4,⟨⟨-6,-5,11,9⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨48,8,⟨⟨57,37,-94,-61⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨50,9,⟨⟨-119,-75,192,121⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨51,9,⟨⟨121,75,-192,-119⟩,[.t (-1),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨46,8,⟨⟨-61,-37,94,57⟩,[.t (-1),.s,.t (-3),.s,.t (-7),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨27,4,⟨⟨9,5,-11,-6⟩,[.t (-1),.s,.t (-6),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,1,⟨⟨1,0,3,1⟩,[.t (0),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨8,1,⟨⟨1,0,-3,1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨36,6,⟨⟨29,-34,6,-7⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨39,7,⟨⟨-55,78,-12,17⟩,[.t (4),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨44,-3,⟨⟨31,-49,19,-30⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨29,5,⟨⟨21,-38,5,-9⟩,[.t (4),.s,.t (-5),.s,.t (-2)],0⟩⟩,⟨22,3,⟨⟨-7,18,-2,5⟩,[.t (3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨30,3,⟨⟨5,-18,2,-7⟩,[.t (2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨35,5,⟨⟨-9,38,-5,21⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨41,7,⟨⟨17,-78,12,-55⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-5)],0⟩⟩,⟨32,6,⟨⟨-7,34,-6,29⟩,[.t (1),.s,.t (-6),.s,.t (-5)],0⟩⟩,⟨16,2,⟨⟨-1,6,0,-1⟩,[.t (-6)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-2,3),(-7,11),(-5,8),(-8,13),(-3,5),(-1,2),(0,1),(1,1),(4,3),(3,2),(5,3),(2,1),(3,1),(4,1),(9,2),(14,3),(5,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end PSL2_13_c12

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
