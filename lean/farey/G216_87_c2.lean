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
namespace G216_87_c2
noncomputable def originalSData : LookupTree (Fin 24) :=
  (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (10)) (.leaf (6)))) (.branch 10 (.leaf (13)) (.branch 11 (.leaf (7)) (.leaf (12)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (11)) (.branch 14 (.leaf (9)) (.leaf (15)))) (.branch 16 (.leaf (14)) (.branch 17 (.leaf (18)) (.leaf (20))))) (.branch 21 (.branch 19 (.leaf (16)) (.branch 20 (.leaf (22)) (.leaf (17)))) (.branch 22 (.leaf (23)) (.branch 23 (.leaf (19)) (.leaf (21)))))))
noncomputable def originalS (p : Fin 24) : Fin 24 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 24) :=
  (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (7)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (12)))) (.branch 10 (.leaf (14)) (.branch 11 (.leaf (1)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (15)) (.branch 14 (.leaf (16)) (.leaf (10)))) (.branch 16 (.leaf (17)) (.branch 17 (.leaf (19)) (.leaf (21))))) (.branch 21 (.branch 19 (.leaf (8)) (.branch 20 (.leaf (20)) (.leaf (13)))) (.branch 22 (.leaf (18)) (.branch 23 (.leaf (23)) (.leaf (22)))))))
noncomputable def originalT (p : Fin 24) : Fin 24 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 24) :=
  (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (8)))) (.branch 10 (.leaf (9)) (.branch 11 (.leaf (10)) (.leaf (11)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (12)) (.branch 14 (.leaf (13)) (.leaf (14)))) (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (17))))) (.branch 21 (.branch 19 (.leaf (18)) (.branch 20 (.leaf (19)) (.leaf (20)))) (.branch 22 (.leaf (21)) (.branch 23 (.leaf (22)) (.leaf (23)))))))
noncomputable def projection (p : Fin 24) : Fin 24 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 24) :=
  (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (4)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (8)))) (.branch 10 (.leaf (9)) (.branch 11 (.leaf (10)) (.leaf (11)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (12)) (.branch 14 (.leaf (13)) (.leaf (14)))) (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (17))))) (.branch 21 (.branch 19 (.leaf (18)) (.branch 20 (.leaf (19)) (.leaf (20)))) (.branch 22 (.leaf (21)) (.branch 23 (.leaf (22)) (.leaf (23)))))))
noncomputable def representative (p : Fin 24) : Fin 24 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 24) :=
  (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (2)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (8)) (.branch 8 (.leaf (10)) (.leaf (6)))) (.branch 10 (.leaf (13)) (.branch 11 (.leaf (7)) (.leaf (12)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (11)) (.branch 14 (.leaf (9)) (.leaf (15)))) (.branch 16 (.leaf (14)) (.branch 17 (.leaf (18)) (.leaf (20))))) (.branch 21 (.branch 19 (.leaf (16)) (.branch 20 (.leaf (22)) (.leaf (17)))) (.branch 22 (.leaf (23)) (.branch 23 (.leaf (19)) (.leaf (21)))))))
noncomputable def S (p : Fin 24) : Fin 24 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 24) :=
  (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (7)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (12)))) (.branch 10 (.leaf (14)) (.branch 11 (.leaf (1)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (15)) (.branch 14 (.leaf (16)) (.leaf (10)))) (.branch 16 (.leaf (17)) (.branch 17 (.leaf (19)) (.leaf (21))))) (.branch 21 (.branch 19 (.leaf (8)) (.branch 20 (.leaf (20)) (.leaf (13)))) (.branch 22 (.leaf (18)) (.branch 23 (.leaf (23)) (.leaf (22)))))))
noncomputable def T (p : Fin 24) : Fin 24 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 24) :=
  (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (10)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (5)) (.leaf (11))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (18)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (14)) (.leaf (7)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (8)) (.branch 14 (.leaf (20)) (.leaf (9)))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (15))))) (.branch 21 (.branch 19 (.leaf (21)) (.branch 20 (.leaf (16)) (.leaf (19)))) (.branch 22 (.leaf (17)) (.branch 23 (.leaf (23)) (.leaf (22)))))))
noncomputable def Ti (p : Fin 24) : Fin 24 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 24) : Fin 24 := T (S p)
theorem quotient_relations : (∀ p : Fin 24, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 24, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 24, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 24, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 24)) := [[0,3,4],[1,2,7],[5,6,12],[8,9,16],[10,11,15],[13,14,17],[18,19,23],[20,21,22]]
noncomputable def verticesIndexData : LookupTree (Fin 24) :=
 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (5)) (.leaf (9)))) (.branch 10 (.leaf (10)) (.branch 11 (.leaf (12)) (.leaf (13)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (8)) (.branch 14 (.leaf (15)) (.leaf (16)))) (.branch 16 (.leaf (14)) (.branch 17 (.leaf (11)) (.leaf (17))))) (.branch 21 (.branch 19 (.leaf (18)) (.branch 20 (.leaf (19)) (.leaf (21)))) (.branch 22 (.leaf (22)) (.branch 23 (.leaf (23)) (.leaf (20)))))))
noncomputable def verticesIndex (p : Fin 24) : Fin 24 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 24) :=
 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (6)) (.leaf (12)))) (.branch 10 (.leaf (8)) (.branch 11 (.leaf (9)) (.leaf (16)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (10)) (.branch 14 (.leaf (11)) (.leaf (15)))) (.branch 16 (.leaf (13)) (.branch 17 (.leaf (14)) (.leaf (17))))) (.branch 21 (.branch 19 (.leaf (18)) (.branch 20 (.leaf (19)) (.leaf (23)))) (.branch 22 (.leaf (20)) (.branch 23 (.leaf (21)) (.leaf (22)))))))
noncomputable def verticesBack (p : Fin 24) : Fin 24 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 24, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 24 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 24, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 24)) := [[0,1],[2,4],[3,5],[6,8],[7,10],[9,13],[11,12],[14,15],[16,18],[17,20],[19,22],[21,23]]
noncomputable def edgesIndexData : LookupTree (Fin 24) :=
 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 10 (.leaf (10)) (.branch 11 (.leaf (9)) (.leaf (12)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (13)) (.branch 14 (.leaf (11)) (.leaf (14)))) (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (18))))) (.branch 21 (.branch 19 (.leaf (17)) (.branch 20 (.leaf (20)) (.leaf (19)))) (.branch 22 (.leaf (22)) (.branch 23 (.leaf (21)) (.leaf (23)))))))
noncomputable def edgesIndex (p : Fin 24) : Fin 24 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 24) :=
 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (5))))) (.branch 9 (.branch 7 (.leaf (6)) (.branch 8 (.leaf (8)) (.leaf (7)))) (.branch 10 (.leaf (10)) (.branch 11 (.leaf (9)) (.leaf (13)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (11)) (.branch 14 (.leaf (12)) (.leaf (14)))) (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (18))))) (.branch 21 (.branch 19 (.leaf (17)) (.branch 20 (.leaf (20)) (.leaf (19)))) (.branch 22 (.leaf (22)) (.branch 23 (.leaf (21)) (.leaf (23)))))))
noncomputable def edgesBack (p : Fin 24) : Fin 24 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 24, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 24 := by decide +kernel
theorem edges_partition : ∀ p : Fin 24, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 24)) := [[0,2],[1,3,6,9,14,10],[4,7,11,5],[8,12,15,17,21,18],[13,16,19,20],[22,23]]
noncomputable def facesIndexData : LookupTree (Fin 24) :=
 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (8)) (.leaf (11))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (9)) (.leaf (12)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (7)) (.leaf (10)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (13)) (.branch 14 (.leaf (18)) (.leaf (6)))) (.branch 16 (.leaf (14)) (.branch 17 (.leaf (19)) (.leaf (15))))) (.branch 21 (.branch 19 (.leaf (17)) (.branch 20 (.leaf (20)) (.leaf (21)))) (.branch 22 (.leaf (16)) (.branch 23 (.leaf (22)) (.leaf (23)))))))
noncomputable def facesIndex (p : Fin 24) : Fin 24 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 24) :=
 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (1)))) (.branch 4 (.leaf (3)) (.branch 5 (.leaf (6)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (14)) (.branch 8 (.leaf (10)) (.leaf (4)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (11)) (.leaf (5)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (8)) (.branch 14 (.leaf (12)) (.leaf (15)))) (.branch 16 (.leaf (17)) (.branch 17 (.leaf (21)) (.leaf (18))))) (.branch 21 (.branch 19 (.leaf (13)) (.branch 20 (.leaf (16)) (.leaf (19)))) (.branch 22 (.leaf (20)) (.branch 23 (.leaf (22)) (.leaf (23)))))))
noncomputable def facesBack (p : Fin 24) : Fin 24 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 24, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 24 := by decide +kernel
theorem faces_partition : ∀ p : Fin 24, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [2,6,4,6,4,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 8 - 12 + 6 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨-1,0,1,-1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨0,1,-1,-2⟩)) (.branch 8 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨1,0,-2,1⟩)))) (.branch 10 (.leaf (⟨0,-1,1,3⟩)) (.branch 11 (.leaf (⟨0,1,-1,1⟩)) (.leaf (⟨1,1,1,2⟩)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (⟨1,1,-2,-1⟩)) (.branch 14 (.leaf (⟨-1,0,-3,-1⟩)) (.leaf (⟨0,-1,1,-2⟩)))) (.branch 16 (.leaf (⟨1,0,2,1⟩)) (.branch 17 (.leaf (⟨-1,-1,3,2⟩)) (.leaf (⟨-1,-1,-2,-3⟩))))) (.branch 21 (.branch 19 (.leaf (⟨-1,1,2,-3⟩)) (.branch 20 (.leaf (⟨1,2,-3,-5⟩)) (.leaf (⟨-1,1,-3,2⟩)))) (.branch 22 (.leaf (⟨1,2,2,5⟩)) (.branch 23 (.leaf (⟨2,1,5,3⟩)) (.leaf (⟨2,1,-5,-2⟩)))))))
noncomputable def liftMatrix (p : Fin 24) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 24) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],4⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],5⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],6⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],7⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],8⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],9⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],10⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],11⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],13⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],14⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],15⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],16⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],17⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],18⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],19⟩,⟨⟨-1,1,-3,2⟩,[.t (0),.s,.t (-3),.s,.t (-1)],20⟩,⟨⟨1,2,2,5⟩,[.t (0),.s,.t (-2),.s,.t (2)],21⟩,⟨⟨2,1,5,3⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (0)],22⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],23⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 24 ∧ ((List.finRange 24).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 24) := [⟨4,1,⟨⟨1,2,0,1⟩,[.t (2)],0⟩⟩,⟨12,3,⟨⟨3,2,4,3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨23,5,⟨⟨9,4,20,9⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨19,4,⟨⟨-11,-4,-30,-11⟩,[.t (0),.s,.t (-3),.s,.t (-4),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨9,2,⟨⟨-1,0,-6,-1⟩,[.t (0),.s,.t (-6),.s,.t (0)],0⟩⟩,⟨13,2,⟨⟨-1,0,6,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨22,4,⟨⟨-11,4,30,-11⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨21,5,⟨⟨9,-4,-20,9⟩,[.t (-1),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨11,3,⟨⟨3,-2,-4,3⟩,[.t (-1),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨2,1,⟨⟨1,-2,0,1⟩,[.t (-2)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-1,2),(-2,5),(-1,3),(0,1),(1,3),(2,5),(1,2),(1,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G216_87_c2

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
