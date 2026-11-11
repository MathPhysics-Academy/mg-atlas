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
namespace A7_c18
noncomputable def originalSData : LookupTree (Fin 84) :=
  (.branch 42 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (7)) (.leaf (9))))) (.branch 7 (.branch 6 (.leaf (8)) (.leaf (12))) (.branch 8 (.leaf (0)) (.branch 9 (.leaf (14)) (.leaf (13)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (17)) (.leaf (18))) (.branch 13 (.leaf (15)) (.branch 14 (.leaf (21)) (.leaf (2))))) (.branch 18 (.branch 16 (.leaf (16)) (.branch 17 (.leaf (6)) (.leaf (22)))) (.branch 19 (.leaf (23)) (.branch 20 (.leaf (26)) (.leaf (28))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (4)) (.leaf (30))) (.branch 24 (.leaf (31)) (.branch 25 (.leaf (33)) (.leaf (35))))) (.branch 28 (.branch 27 (.leaf (32)) (.leaf (37))) (.branch 29 (.leaf (24)) (.branch 30 (.leaf (39)) (.leaf (10)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (11)) (.leaf (42))) (.branch 34 (.leaf (20)) (.branch 35 (.leaf (44)) (.leaf (41))))) (.branch 39 (.branch 37 (.leaf (46)) (.branch 38 (.leaf (43)) (.leaf (49)))) (.branch 40 (.leaf (34)) (.branch 41 (.leaf (52)) (.leaf (54)))))))) (.branch 63 (.branch 52 (.branch 47 (.branch 44 (.branch 43 (.leaf (19)) (.leaf (56))) (.branch 45 (.leaf (29)) (.branch 46 (.leaf (59)) (.leaf (55))))) (.branch 49 (.branch 48 (.leaf (48)) (.leaf (62))) (.branch 50 (.leaf (57)) (.branch 51 (.leaf (58)) (.leaf (50)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (45)) (.leaf (61))) (.branch 55 (.leaf (25)) (.branch 56 (.leaf (67)) (.leaf (27))))) (.branch 60 (.branch 58 (.leaf (69)) (.branch 59 (.leaf (70)) (.leaf (40)))) (.branch 61 (.leaf (73)) (.branch 62 (.leaf (60)) (.leaf (68))))))) (.branch 73 (.branch 68 (.branch 65 (.branch 64 (.leaf (75)) (.leaf (76))) (.branch 66 (.leaf (72)) (.branch 67 (.leaf (65)) (.leaf (36))))) (.branch 70 (.branch 69 (.leaf (47)) (.leaf (38))) (.branch 71 (.leaf (51)) (.branch 72 (.leaf (66)) (.leaf (71)))))) (.branch 78 (.branch 75 (.branch 74 (.leaf (53)) (.leaf (77))) (.branch 76 (.leaf (78)) (.branch 77 (.leaf (79)) (.leaf (80))))) (.branch 81 (.branch 79 (.leaf (81)) (.branch 80 (.leaf (82)) (.leaf (83)))) (.branch 82 (.leaf (63)) (.branch 83 (.leaf (64)) (.leaf (74)))))))))
noncomputable def originalS (p : Fin 84) : Fin 84 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 84) :=
  (.branch 42 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.branch 4 (.leaf (8)) (.leaf (10))))) (.branch 7 (.branch 6 (.leaf (11)) (.leaf (3))) (.branch 8 (.leaf (13)) (.branch 9 (.leaf (15)) (.leaf (16)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (18)) (.leaf (19))) (.branch 13 (.leaf (20)) (.branch 14 (.leaf (22)) (.leaf (23))))) (.branch 18 (.branch 16 (.leaf (0)) (.branch 17 (.leaf (24)) (.leaf (25)))) (.branch 19 (.leaf (1)) (.branch 20 (.leaf (27)) (.leaf (29))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (12)) (.leaf (31))) (.branch 24 (.leaf (32)) (.branch 25 (.leaf (34)) (.leaf (36))))) (.branch 28 (.branch 27 (.leaf (30)) (.leaf (38))) (.branch 29 (.leaf (5)) (.branch 30 (.leaf (40)) (.leaf (41)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (7)) (.leaf (43))) (.branch 34 (.leaf (14)) (.branch 35 (.leaf (45)) (.leaf (9))))) (.branch 39 (.branch 37 (.leaf (47)) (.branch 38 (.leaf (48)) (.leaf (50)))) (.branch 40 (.leaf (51)) (.branch 41 (.leaf (53)) (.leaf (55)))))))) (.branch 63 (.branch 52 (.branch 47 (.branch 44 (.branch 43 (.leaf (17)) (.leaf (57))) (.branch 45 (.leaf (58)) (.branch 46 (.leaf (60)) (.leaf (61))))) (.branch 49 (.branch 48 (.leaf (42)) (.leaf (63))) (.branch 50 (.leaf (64)) (.branch 51 (.leaf (28)) (.leaf (65)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (66)) (.leaf (54))) (.branch 55 (.leaf (21)) (.branch 56 (.leaf (62)) (.leaf (68))))) (.branch 60 (.branch 58 (.leaf (70)) (.branch 59 (.leaf (71)) (.leaf (72)))) (.branch 61 (.leaf (35)) (.branch 62 (.leaf (74)) (.leaf (26))))))) (.branch 73 (.branch 68 (.branch 65 (.branch 64 (.leaf (76)) (.leaf (77))) (.branch 66 (.leaf (39)) (.branch 67 (.leaf (49)) (.leaf (73))))) (.branch 70 (.branch 69 (.leaf (78)) (.leaf (79))) (.branch 71 (.leaf (33)) (.branch 72 (.leaf (44)) (.leaf (69)))))) (.branch 78 (.branch 75 (.branch 74 (.leaf (80)) (.leaf (75))) (.branch 76 (.leaf (46)) (.branch 77 (.leaf (37)) (.leaf (52))))) (.branch 81 (.branch 79 (.leaf (82)) (.branch 80 (.leaf (83)) (.leaf (81)))) (.branch 82 (.leaf (67)) (.branch 83 (.leaf (56)) (.leaf (59)))))))))
noncomputable def originalT (p : Fin 84) : Fin 84 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 42) :=
  (.branch 42 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (0)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (4)) (.leaf (5))) (.branch 8 (.leaf (1)) (.branch 9 (.leaf (2)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (8))) (.branch 13 (.leaf (9)) (.branch 14 (.leaf (3)) (.leaf (4))))) (.branch 18 (.branch 16 (.leaf (5)) (.branch 17 (.leaf (9)) (.leaf (10)))) (.branch 19 (.leaf (11)) (.branch 20 (.leaf (12)) (.leaf (13))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (6)) (.leaf (7))) (.branch 24 (.leaf (8)) (.branch 25 (.leaf (13)) (.leaf (14))))) (.branch 28 (.branch 27 (.leaf (15)) (.leaf (16))) (.branch 29 (.leaf (17)) (.branch 30 (.leaf (18)) (.leaf (10)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (11)) (.leaf (12))) (.branch 34 (.leaf (17)) (.branch 35 (.leaf (18)) (.leaf (19))))) (.branch 39 (.branch 37 (.leaf (20)) (.branch 38 (.leaf (21)) (.leaf (22)))) (.branch 40 (.leaf (23)) (.branch 41 (.leaf (24)) (.leaf (14)))))))) (.branch 63 (.branch 52 (.branch 47 (.branch 44 (.branch 43 (.leaf (15)) (.leaf (16))) (.branch 45 (.leaf (23)) (.branch 46 (.leaf (24)) (.leaf (25))))) (.branch 49 (.branch 48 (.leaf (26)) (.leaf (27))) (.branch 50 (.leaf (28)) (.branch 51 (.leaf (29)) (.leaf (30)))))) (.branch 57 (.branch 54 (.branch 53 (.leaf (31)) (.leaf (32))) (.branch 55 (.leaf (19)) (.branch 56 (.leaf (20)) (.leaf (21))))) (.branch 60 (.branch 58 (.leaf (22)) (.branch 59 (.leaf (30)) (.leaf (31)))) (.branch 61 (.leaf (32)) (.branch 62 (.leaf (33)) (.leaf (26))))))) (.branch 73 (.branch 68 (.branch 65 (.branch 64 (.leaf (34)) (.leaf (35))) (.branch 66 (.leaf (36)) (.branch 67 (.leaf (37)) (.leaf (25))))) (.branch 70 (.branch 69 (.leaf (27)) (.leaf (28))) (.branch 71 (.leaf (29)) (.branch 72 (.leaf (36)) (.leaf (37)))))) (.branch 78 (.branch 75 (.branch 74 (.leaf (33)) (.leaf (38))) (.branch 76 (.leaf (39)) (.branch 77 (.leaf (40)) (.leaf (41))))) (.branch 81 (.branch 79 (.leaf (34)) (.branch 80 (.leaf (35)) (.leaf (38)))) (.branch 82 (.leaf (39)) (.branch 83 (.leaf (40)) (.leaf (41)))))))))
noncomputable def projection (p : Fin 84) : Fin 42 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 84) :=
  (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (5))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (9))) (.branch 8 (.leaf (10)) (.branch 9 (.leaf (11)) (.leaf (12)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (17)) (.leaf (18))) (.branch 13 (.leaf (19)) (.branch 14 (.leaf (20)) (.leaf (25))))) (.branch 18 (.branch 16 (.leaf (26)) (.branch 17 (.leaf (27)) (.leaf (28)))) (.branch 19 (.leaf (29)) (.branch 20 (.leaf (35)) (.leaf (36))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (37)) (.leaf (38))) (.branch 24 (.leaf (39)) (.branch 25 (.leaf (40)) (.leaf (46))))) (.branch 28 (.branch 27 (.leaf (47)) (.leaf (48))) (.branch 29 (.leaf (49)) (.branch 30 (.leaf (50)) (.leaf (51)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (52)) (.leaf (53))) (.branch 34 (.leaf (61)) (.branch 35 (.leaf (63)) (.leaf (64))))) (.branch 39 (.branch 37 (.leaf (65)) (.branch 38 (.leaf (66)) (.leaf (74)))) (.branch 40 (.leaf (75)) (.branch 41 (.leaf (76)) (.leaf (77))))))))
noncomputable def representative (p : Fin 42) : Fin 84 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 42) :=
  (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (6)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (9)) (.leaf (3))) (.branch 8 (.leaf (10)) (.branch 9 (.leaf (11)) (.leaf (5)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (8))) (.branch 13 (.leaf (15)) (.branch 14 (.leaf (17)) (.leaf (19))))) (.branch 18 (.branch 16 (.leaf (12)) (.branch 17 (.leaf (21)) (.leaf (13)))) (.branch 19 (.leaf (23)) (.branch 20 (.leaf (14)) (.leaf (25))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (16)) (.leaf (28))) (.branch 24 (.leaf (18)) (.branch 25 (.leaf (31)) (.leaf (20))))) (.branch 28 (.branch 27 (.leaf (27)) (.leaf (26))) (.branch 29 (.leaf (22)) (.branch 30 (.leaf (30)) (.leaf (29)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (24)) (.leaf (33))) (.branch 34 (.leaf (32)) (.branch 35 (.leaf (39)) (.leaf (40))))) (.branch 39 (.branch 37 (.leaf (37)) (.branch 38 (.leaf (36)) (.leaf (41)))) (.branch 40 (.leaf (34)) (.branch 41 (.leaf (35)) (.leaf (38))))))))
noncomputable def S (p : Fin 42) : Fin 42 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 42) :=
  (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (7)) (.leaf (8))))) (.branch 7 (.branch 6 (.leaf (0)) (.leaf (9))) (.branch 8 (.leaf (11)) (.branch 9 (.leaf (12)) (.leaf (13)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (14)) (.leaf (1))) (.branch 13 (.leaf (16)) (.branch 14 (.leaf (18)) (.leaf (20))))) (.branch 18 (.branch 16 (.leaf (10)) (.branch 17 (.leaf (22)) (.leaf (4)))) (.branch 19 (.leaf (24)) (.branch 20 (.leaf (6)) (.leaf (26))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (27)) (.leaf (29))) (.branch 24 (.leaf (30)) (.branch 25 (.leaf (32)) (.leaf (33))))) (.branch 28 (.branch 27 (.leaf (15)) (.leaf (34))) (.branch 29 (.leaf (35)) (.branch 30 (.leaf (17)) (.leaf (36)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (37)) (.leaf (19))) (.branch 34 (.leaf (38)) (.branch 35 (.leaf (40)) (.leaf (41))))) (.branch 39 (.branch 37 (.leaf (23)) (.branch 38 (.leaf (28)) (.leaf (39)))) (.branch 40 (.leaf (25)) (.branch 41 (.leaf (21)) (.leaf (31))))))))
noncomputable def T (p : Fin 42) : Fin 42 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 42) :=
  (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (5)) (.leaf (11))) (.branch 3 (.leaf (0)) (.branch 4 (.leaf (1)) (.leaf (17))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (19))) (.branch 8 (.leaf (3)) (.branch 9 (.leaf (4)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (15)) (.leaf (7))) (.branch 13 (.leaf (8)) (.branch 14 (.leaf (9)) (.leaf (10))))) (.branch 18 (.branch 16 (.leaf (26)) (.branch 17 (.leaf (12)) (.leaf (29)))) (.branch 19 (.leaf (13)) (.branch 20 (.leaf (32)) (.leaf (14))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (40)) (.leaf (16))) (.branch 24 (.leaf (36)) (.branch 25 (.leaf (18)) (.leaf (39))))) (.branch 28 (.branch 27 (.leaf (20)) (.leaf (21))) (.branch 29 (.leaf (37)) (.branch 30 (.leaf (22)) (.leaf (23)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (41)) (.leaf (24))) (.branch 34 (.leaf (25)) (.branch 35 (.leaf (27)) (.leaf (28))))) (.branch 39 (.branch 37 (.leaf (30)) (.branch 38 (.leaf (31)) (.leaf (33)))) (.branch 40 (.leaf (38)) (.branch 41 (.leaf (34)) (.leaf (35))))))))
noncomputable def Ti (p : Fin 42) : Fin 42 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 42) : Fin 42 := T (S p)
theorem quotient_relations : (∀ p : Fin 42, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 84, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 84, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 42, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 42)) := [[0,3,9],[1,2,8],[4,5,13],[6,7,14],[10,11,12],[15,16,27],[17,18,30],[19,20,33],[21,22,35],[23,24,37],[25,26,34],[28,29,36],[31,32,38],[39,40,41]]
noncomputable def verticesIndexData : LookupTree (Fin 42) :=
 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.branch 4 (.leaf (1)) (.leaf (6))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (9))) (.branch 8 (.leaf (10)) (.branch 9 (.leaf (5)) (.leaf (2)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (12)) (.leaf (13))) (.branch 13 (.leaf (14)) (.branch 14 (.leaf (8)) (.leaf (11))))) (.branch 18 (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (18)))) (.branch 19 (.leaf (19)) (.branch 20 (.leaf (21)) (.leaf (22))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (24)) (.leaf (25))) (.branch 24 (.leaf (27)) (.branch 25 (.leaf (28)) (.leaf (30))))) (.branch 28 (.branch 27 (.leaf (31)) (.leaf (17))) (.branch 29 (.leaf (33)) (.branch 30 (.leaf (34)) (.leaf (20)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (36)) (.leaf (37))) (.branch 34 (.leaf (23)) (.branch 35 (.leaf (32)) (.leaf (26))))) (.branch 39 (.branch 37 (.leaf (35)) (.branch 38 (.leaf (29)) (.leaf (38)))) (.branch 40 (.leaf (39)) (.branch 41 (.leaf (40)) (.leaf (41))))))))
noncomputable def verticesIndex (p : Fin 42) : Fin 42 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 42) :=
 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (9)) (.branch 4 (.leaf (1)) (.leaf (2))))) (.branch 7 (.branch 6 (.leaf (8)) (.leaf (4))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (13)) (.leaf (6)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (7)) (.leaf (14))) (.branch 13 (.leaf (10)) (.branch 14 (.leaf (11)) (.leaf (12))))) (.branch 18 (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (27)))) (.branch 19 (.leaf (17)) (.branch 20 (.leaf (18)) (.leaf (30))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (19)) (.leaf (20))) (.branch 24 (.leaf (33)) (.branch 25 (.leaf (21)) (.leaf (22))))) (.branch 28 (.branch 27 (.leaf (35)) (.leaf (23))) (.branch 29 (.leaf (24)) (.branch 30 (.leaf (37)) (.leaf (25)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (26)) (.leaf (34))) (.branch 34 (.leaf (28)) (.branch 35 (.leaf (29)) (.leaf (36))))) (.branch 39 (.branch 37 (.leaf (31)) (.branch 38 (.leaf (32)) (.leaf (38)))) (.branch 40 (.leaf (39)) (.branch 41 (.leaf (40)) (.leaf (41))))))))
noncomputable def verticesBack (p : Fin 42) : Fin 42 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 42, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 42 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 42, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 42)) := [[0,1],[2,4],[3,6],[5,9],[7,10],[8,11],[12,15],[13,17],[14,19],[16,21],[18,23],[20,25],[22,28],[24,31],[26,27],[29,30],[32,33],[34,39],[35,40],[36,37],[38,41]]
noncomputable def edgesIndexData : LookupTree (Fin 42) :=
 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (5))) (.branch 8 (.leaf (8)) (.branch 9 (.leaf (10)) (.leaf (7)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (9)) (.leaf (11))) (.branch 13 (.leaf (12)) (.branch 14 (.leaf (14)) (.leaf (16))))) (.branch 18 (.branch 16 (.leaf (13)) (.branch 17 (.leaf (18)) (.leaf (15)))) (.branch 19 (.leaf (20)) (.branch 20 (.leaf (17)) (.leaf (22))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (19)) (.leaf (24))) (.branch 24 (.leaf (21)) (.branch 25 (.leaf (26)) (.leaf (23))))) (.branch 28 (.branch 27 (.leaf (28)) (.leaf (29))) (.branch 29 (.leaf (25)) (.branch 30 (.leaf (30)) (.leaf (31)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (27)) (.leaf (32))) (.branch 34 (.leaf (33)) (.branch 35 (.leaf (34)) (.leaf (36))))) (.branch 39 (.branch 37 (.leaf (38)) (.branch 38 (.leaf (39)) (.leaf (40)))) (.branch 40 (.leaf (35)) (.branch 41 (.leaf (37)) (.leaf (41))))))))
noncomputable def edgesIndex (p : Fin 42) : Fin 42 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 42) :=
 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.branch 4 (.leaf (4)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (6)) (.leaf (5))) (.branch 8 (.leaf (9)) (.branch 9 (.leaf (7)) (.leaf (10)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (8)) (.leaf (11))) (.branch 13 (.leaf (12)) (.branch 14 (.leaf (15)) (.leaf (13))))) (.branch 18 (.branch 16 (.leaf (17)) (.branch 17 (.leaf (14)) (.leaf (19)))) (.branch 19 (.leaf (16)) (.branch 20 (.leaf (21)) (.leaf (18))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (23)) (.leaf (20))) (.branch 24 (.leaf (25)) (.branch 25 (.leaf (22)) (.leaf (28))))) (.branch 28 (.branch 27 (.leaf (24)) (.leaf (31))) (.branch 29 (.leaf (26)) (.branch 30 (.leaf (27)) (.leaf (29)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (30)) (.leaf (32))) (.branch 34 (.leaf (33)) (.branch 35 (.leaf (34)) (.leaf (39))))) (.branch 39 (.branch 37 (.leaf (35)) (.branch 38 (.leaf (40)) (.leaf (36)))) (.branch 40 (.leaf (37)) (.branch 41 (.leaf (38)) (.leaf (41))))))))
noncomputable def edgesBack (p : Fin 42) : Fin 42 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 42, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 42 := by decide +kernel
theorem edges_partition : ∀ p : Fin 42, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 42)) := [[0,2,5],[1,3,7,11],[4,8,12,16,22,29,17],[6,9,13,18,24,32,19],[10,14,20,26,15],[21,27,34,40],[23,30,36],[25,33,38,39],[28,35,41,31,37]]
noncomputable def facesIndexData : LookupTree (Fin 42) :=
 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.branch 4 (.leaf (4)) (.leaf (7))))) (.branch 7 (.branch 6 (.leaf (2)) (.leaf (14))) (.branch 8 (.leaf (5)) (.branch 9 (.leaf (8)) (.leaf (15)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (21)) (.leaf (6))) (.branch 13 (.leaf (9)) (.branch 14 (.leaf (16)) (.leaf (22))))) (.branch 18 (.branch 16 (.leaf (25)) (.branch 17 (.leaf (10)) (.leaf (13)))) (.branch 19 (.leaf (17)) (.branch 20 (.leaf (20)) (.leaf (23))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (26)) (.leaf (11))) (.branch 24 (.leaf (30)) (.branch 25 (.leaf (18)) (.leaf (33))))) (.branch 28 (.branch 27 (.leaf (24)) (.leaf (27))) (.branch 29 (.leaf (37)) (.branch 30 (.leaf (12)) (.leaf (31)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (40)) (.leaf (19))) (.branch 34 (.leaf (34)) (.branch 35 (.leaf (28)) (.leaf (38))))) (.branch 39 (.branch 37 (.leaf (32)) (.branch 38 (.leaf (41)) (.leaf (35)))) (.branch 40 (.leaf (36)) (.branch 41 (.leaf (29)) (.leaf (39))))))))
noncomputable def facesIndex (p : Fin 42) : Fin 42 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 42) :=
 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.branch 4 (.leaf (1)) (.leaf (3))))) (.branch 7 (.branch 6 (.leaf (7)) (.leaf (11))) (.branch 8 (.leaf (4)) (.branch 9 (.leaf (8)) (.leaf (12)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (16)) (.leaf (22))) (.branch 13 (.leaf (29)) (.branch 14 (.leaf (17)) (.leaf (6))))) (.branch 18 (.branch 16 (.leaf (9)) (.branch 17 (.leaf (13)) (.leaf (18)))) (.branch 19 (.leaf (24)) (.branch 20 (.leaf (32)) (.leaf (19))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (10)) (.leaf (14))) (.branch 24 (.leaf (20)) (.branch 25 (.leaf (26)) (.leaf (15))))) (.branch 28 (.branch 27 (.leaf (21)) (.leaf (27))) (.branch 29 (.leaf (34)) (.branch 30 (.leaf (40)) (.leaf (23)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (30)) (.leaf (36))) (.branch 34 (.leaf (25)) (.branch 35 (.leaf (33)) (.leaf (38))))) (.branch 39 (.branch 37 (.leaf (39)) (.branch 38 (.leaf (28)) (.leaf (35)))) (.branch 40 (.leaf (41)) (.branch 41 (.leaf (31)) (.leaf (37))))))))
noncomputable def facesBack (p : Fin 42) : Fin 42 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 42, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 42 := by decide +kernel
theorem faces_partition : ∀ p : Fin 42, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [3,4,7,7,5,4,3,4,5] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 14 - 21 + 9 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 21 (.branch 10 (.branch 5 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.leaf (⟨-1,1,-1,0⟩))))) (.branch 7 (.branch 6 (.leaf (⟨1,2,0,1⟩)) (.leaf (⟨-1,0,1,-1⟩))) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.branch 9 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨-1,-1,1,0⟩)))))) (.branch 15 (.branch 12 (.branch 11 (.leaf (⟨1,0,2,1⟩)) (.leaf (⟨0,1,-1,1⟩))) (.branch 13 (.leaf (⟨1,1,1,2⟩)) (.branch 14 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨1,1,-2,-1⟩))))) (.branch 18 (.branch 16 (.leaf (⟨1,-1,2,-1⟩)) (.branch 17 (.leaf (⟨-1,-2,-1,-3⟩)) (.leaf (⟨1,-2,1,-1⟩)))) (.branch 19 (.leaf (⟨-2,-3,-1,-2⟩)) (.branch 20 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-2,2,3⟩))))))) (.branch 31 (.branch 26 (.branch 23 (.branch 22 (.leaf (⟨-2,1,-3,1⟩)) (.leaf (⟨1,3,1,4⟩))) (.branch 24 (.leaf (⟨-3,2,-2,1⟩)) (.branch 25 (.leaf (⟨2,5,1,3⟩)) (.leaf (⟨-2,1,3,-2⟩))))) (.branch 28 (.branch 27 (.leaf (⟨1,3,-2,-5⟩)) (.leaf (⟨-2,-1,-3,-2⟩))) (.branch 29 (.leaf (⟨4,1,3,1⟩)) (.branch 30 (.leaf (⟨-1,3,-1,2⟩)) (.leaf (⟨-3,-1,-2,-1⟩)))))) (.branch 36 (.branch 33 (.branch 32 (.leaf (⟨3,1,-4,-1⟩)) (.leaf (⟨-1,2,1,-3⟩))) (.branch 34 (.leaf (⟨-2,-1,3,1⟩)) (.branch 35 (.leaf (⟨3,2,-5,-3⟩)) (.leaf (⟨3,2,4,3⟩))))) (.branch 39 (.branch 37 (.leaf (⟨3,4,2,3⟩)) (.branch 38 (.leaf (⟨5,3,3,2⟩)) (.leaf (⟨2,3,-3,-4⟩)))) (.branch 40 (.leaf (⟨2,-3,-3,5⟩)) (.branch 41 (.leaf (⟨-3,-5,5,8⟩)) (.leaf (⟨-5,-2,8,3⟩))))))))
noncomputable def liftMatrix (p : Fin 42) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 42) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],10⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],11⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],12⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],13⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],14⟩,⟨⟨1,-1,2,-1⟩,[.t (0),.s,.t (-2),.s,.t (-1)],15⟩,⟨⟨-1,-2,-1,-3⟩,[.t (1),.s,.t (3)],16⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],17⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],18⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],19⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],20⟩,⟨⟨-2,1,-3,1⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-1)],21⟩,⟨⟨1,3,1,4⟩,[.t (1),.s,.t (4)],22⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],23⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],24⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],25⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],26⟩,⟨⟨-2,-1,-3,-2⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (0)],27⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],28⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],29⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],30⟩,⟨⟨3,1,-4,-1⟩,[.t (-1),.s,.t (-4),.s,.t (0)],31⟩,⟨⟨-1,2,1,-3⟩,[.t (-1),.s,.t (-3)],32⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],33⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],34⟩,⟨⟨3,2,4,3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],35⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],36⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],37⟩,⟨⟨2,3,-3,-4⟩,[.t (-1),.s,.t (-3),.s,.t (1)],38⟩,⟨⟨2,-3,-3,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2)],39⟩,⟨⟨-3,-5,5,8⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (1)],40⟩,⟨⟨-5,-2,8,3⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (0)],41⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 42 ∧ ((List.finRange 42).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 42) := [⟨9,1,⟨⟨-1,-3,0,-1⟩,[.t (3)],0⟩⟩,⟨31,4,⟨⟨13,11,7,6⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨38,8,⟨⟨23,16,-36,-25⟩,[.t (-1),.s,.t (-3),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨41,8,⟨⟨-25,-16,36,23⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨40,6,⟨⟨-31,-19,-44,-27⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨26,5,⟨⟨9,5,16,9⟩,[.t (0),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,2,⟨⟨-1,0,-4,-1⟩,[.t (0),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨10,2,⟨⟨-1,0,4,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨27,5,⟨⟨9,-5,-16,9⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨35,6,⟨⟨-27,19,44,-31⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨22,3,⟨⟨8,-7,7,-6⟩,[.t (1),.s,.t (-7),.s,.t (-1)],0⟩⟩,⟨28,3,⟨⟨-6,7,-7,8⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨36,7,⟨⟨19,-27,12,-17⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨37,7,⟨⟨-17,27,-12,19⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨24,4,⟨⟨6,-11,-7,13⟩,[.t (-1),.s,.t (-7),.s,.t (-2)],0⟩⟩,⟨5,1,⟨⟨-1,3,0,-1⟩,[.t (-3)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-3,4),(-2,3),(-5,8),(-3,5),(-1,2),(0,1),(1,2),(2,3),(3,4),(1,1),(4,3),(3,2),(5,3),(2,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end A7_c18

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
