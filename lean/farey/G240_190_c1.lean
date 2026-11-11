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
namespace G240_190_c1
noncomputable def originalSData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (2))) (.branch 6 (.leaf (7)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (11))) (.branch 10 (.leaf (13)) (.leaf (15)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (18))) (.branch 14 (.leaf (9)) (.leaf (19)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (10)) (.branch 17 (.leaf (21)) (.leaf (23)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (14))) (.branch 21 (.leaf (24)) (.leaf (16))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (27)) (.leaf (17))) (.branch 25 (.leaf (20)) (.leaf (30)))) (.branch 28 (.branch 27 (.leaf (32)) (.leaf (22))) (.branch 29 (.leaf (35)) (.leaf (37))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (25)) (.branch 32 (.leaf (40)) (.leaf (26)))) (.branch 35 (.branch 34 (.leaf (42)) (.leaf (44))) (.branch 36 (.leaf (28)) (.leaf (47))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (29)) (.leaf (48))) (.branch 40 (.leaf (50)) (.leaf (31)))) (.branch 43 (.branch 42 (.leaf (53)) (.leaf (33))) (.branch 44 (.leaf (54)) (.leaf (34)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (55)) (.branch 47 (.leaf (56)) (.leaf (36)))) (.branch 50 (.branch 49 (.leaf (38)) (.leaf (57))) (.branch 51 (.leaf (39)) (.leaf (58))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (59)) (.leaf (41))) (.branch 55 (.leaf (43)) (.leaf (45)))) (.branch 58 (.branch 57 (.leaf (46)) (.leaf (49))) (.branch 59 (.leaf (51)) (.leaf (52))))))))
noncomputable def originalS (p : Fin 60) : Fin 60 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (8)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (10)) (.leaf (12))) (.branch 10 (.leaf (14)) (.leaf (16)))) (.branch 13 (.branch 12 (.leaf (17)) (.leaf (13))) (.branch 14 (.leaf (0)) (.leaf (20)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (22)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (23)) (.leaf (18))) (.branch 21 (.leaf (25)) (.leaf (26))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (28)) (.leaf (7))) (.branch 25 (.leaf (29)) (.leaf (31)))) (.branch 28 (.branch 27 (.leaf (33)) (.leaf (34))) (.branch 29 (.leaf (36)) (.leaf (38))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (39)) (.branch 32 (.leaf (41)) (.leaf (15)))) (.branch 35 (.branch 34 (.leaf (43)) (.leaf (45))) (.branch 36 (.leaf (46)) (.leaf (37))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (19)) (.leaf (49))) (.branch 40 (.leaf (51)) (.leaf (52)))) (.branch 43 (.branch 42 (.leaf (32)) (.leaf (53))) (.branch 44 (.leaf (50)) (.leaf (21)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (48)) (.branch 47 (.leaf (35)) (.leaf (56)))) (.branch 50 (.branch 49 (.leaf (47)) (.leaf (44))) (.branch 51 (.leaf (24)) (.leaf (42))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (40)) (.leaf (59))) (.branch 55 (.leaf (58)) (.leaf (57)))) (.branch 58 (.branch 57 (.leaf (27)) (.leaf (55))) (.branch 59 (.leaf (54)) (.leaf (30))))))))
noncomputable def originalT (p : Fin 60) : Fin 60 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (5)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (8))) (.branch 10 (.leaf (9)) (.leaf (10)))) (.branch 13 (.branch 12 (.leaf (11)) (.leaf (12))) (.branch 14 (.leaf (13)) (.leaf (14)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (17)))) (.branch 20 (.branch 19 (.leaf (18)) (.leaf (19))) (.branch 21 (.leaf (20)) (.leaf (21))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (22)) (.leaf (23))) (.branch 25 (.leaf (24)) (.leaf (25)))) (.branch 28 (.branch 27 (.leaf (26)) (.leaf (27))) (.branch 29 (.leaf (28)) (.leaf (29))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (30)) (.branch 32 (.leaf (31)) (.leaf (32)))) (.branch 35 (.branch 34 (.leaf (33)) (.leaf (34))) (.branch 36 (.leaf (35)) (.leaf (36))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (37)) (.leaf (38))) (.branch 40 (.leaf (39)) (.leaf (40)))) (.branch 43 (.branch 42 (.leaf (41)) (.leaf (42))) (.branch 44 (.leaf (43)) (.leaf (44)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (45)) (.branch 47 (.leaf (46)) (.leaf (47)))) (.branch 50 (.branch 49 (.leaf (48)) (.leaf (49))) (.branch 51 (.leaf (50)) (.leaf (51))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (52)) (.leaf (53))) (.branch 55 (.leaf (54)) (.leaf (55)))) (.branch 58 (.branch 57 (.leaf (56)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (59))))))))
noncomputable def projection (p : Fin 60) : Fin 60 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (3)) (.leaf (4))) (.branch 6 (.leaf (5)) (.leaf (6))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (8))) (.branch 10 (.leaf (9)) (.leaf (10)))) (.branch 13 (.branch 12 (.leaf (11)) (.leaf (12))) (.branch 14 (.leaf (13)) (.leaf (14)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (17)))) (.branch 20 (.branch 19 (.leaf (18)) (.leaf (19))) (.branch 21 (.leaf (20)) (.leaf (21))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (22)) (.leaf (23))) (.branch 25 (.leaf (24)) (.leaf (25)))) (.branch 28 (.branch 27 (.leaf (26)) (.leaf (27))) (.branch 29 (.leaf (28)) (.leaf (29))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (30)) (.branch 32 (.leaf (31)) (.leaf (32)))) (.branch 35 (.branch 34 (.leaf (33)) (.leaf (34))) (.branch 36 (.leaf (35)) (.leaf (36))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (37)) (.leaf (38))) (.branch 40 (.leaf (39)) (.leaf (40)))) (.branch 43 (.branch 42 (.leaf (41)) (.leaf (42))) (.branch 44 (.leaf (43)) (.leaf (44)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (45)) (.branch 47 (.leaf (46)) (.leaf (47)))) (.branch 50 (.branch 49 (.leaf (48)) (.leaf (49))) (.branch 51 (.leaf (50)) (.leaf (51))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (52)) (.leaf (53))) (.branch 55 (.leaf (54)) (.leaf (55)))) (.branch 58 (.branch 57 (.leaf (56)) (.leaf (57))) (.branch 59 (.leaf (58)) (.leaf (59))))))))
noncomputable def representative (p : Fin 60) : Fin 60 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (6)) (.leaf (2))) (.branch 6 (.leaf (7)) (.leaf (3))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (11))) (.branch 10 (.leaf (13)) (.leaf (15)))) (.branch 13 (.branch 12 (.leaf (8)) (.leaf (18))) (.branch 14 (.leaf (9)) (.leaf (19)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (10)) (.branch 17 (.leaf (21)) (.leaf (23)))) (.branch 20 (.branch 19 (.leaf (12)) (.leaf (14))) (.branch 21 (.leaf (24)) (.leaf (16))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (27)) (.leaf (17))) (.branch 25 (.leaf (20)) (.leaf (30)))) (.branch 28 (.branch 27 (.leaf (32)) (.leaf (22))) (.branch 29 (.leaf (35)) (.leaf (37))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (25)) (.branch 32 (.leaf (40)) (.leaf (26)))) (.branch 35 (.branch 34 (.leaf (42)) (.leaf (44))) (.branch 36 (.leaf (28)) (.leaf (47))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (29)) (.leaf (48))) (.branch 40 (.leaf (50)) (.leaf (31)))) (.branch 43 (.branch 42 (.leaf (53)) (.leaf (33))) (.branch 44 (.leaf (54)) (.leaf (34)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (55)) (.branch 47 (.leaf (56)) (.leaf (36)))) (.branch 50 (.branch 49 (.leaf (38)) (.leaf (57))) (.branch 51 (.leaf (39)) (.leaf (58))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (59)) (.leaf (41))) (.branch 55 (.leaf (43)) (.leaf (45)))) (.branch 58 (.branch 57 (.leaf (46)) (.leaf (49))) (.branch 59 (.leaf (51)) (.leaf (52))))))))
noncomputable def S (p : Fin 60) : Fin 60 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (8)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (10)) (.leaf (12))) (.branch 10 (.leaf (14)) (.leaf (16)))) (.branch 13 (.branch 12 (.leaf (17)) (.leaf (13))) (.branch 14 (.leaf (0)) (.leaf (20)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (4)) (.branch 17 (.leaf (22)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (23)) (.leaf (18))) (.branch 21 (.leaf (25)) (.leaf (26))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (28)) (.leaf (7))) (.branch 25 (.leaf (29)) (.leaf (31)))) (.branch 28 (.branch 27 (.leaf (33)) (.leaf (34))) (.branch 29 (.leaf (36)) (.leaf (38))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (39)) (.branch 32 (.leaf (41)) (.leaf (15)))) (.branch 35 (.branch 34 (.leaf (43)) (.leaf (45))) (.branch 36 (.leaf (46)) (.leaf (37))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (19)) (.leaf (49))) (.branch 40 (.leaf (51)) (.leaf (52)))) (.branch 43 (.branch 42 (.leaf (32)) (.leaf (53))) (.branch 44 (.leaf (50)) (.leaf (21)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (48)) (.branch 47 (.leaf (35)) (.leaf (56)))) (.branch 50 (.branch 49 (.leaf (47)) (.leaf (44))) (.branch 51 (.leaf (24)) (.leaf (42))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (40)) (.leaf (59))) (.branch 55 (.leaf (58)) (.leaf (57)))) (.branch 58 (.branch 57 (.leaf (27)) (.leaf (55))) (.branch 59 (.leaf (54)) (.leaf (30))))))))
noncomputable def T (p : Fin 60) : Fin 60 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 60) :=
  (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (13)) (.branch 2 (.leaf (3)) (.leaf (0)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (15))) (.branch 6 (.leaf (2)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (23)) (.leaf (5))) (.branch 10 (.leaf (6)) (.leaf (7)))) (.branch 13 (.branch 12 (.leaf (17)) (.leaf (8))) (.branch 14 (.leaf (12)) (.leaf (9)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (32)) (.branch 17 (.leaf (10)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (19)) (.leaf (37))) (.branch 21 (.leaf (14)) (.leaf (44))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (16)) (.leaf (18))) (.branch 25 (.leaf (50)) (.leaf (20)))) (.branch 28 (.branch 27 (.leaf (21)) (.leaf (56))) (.branch 29 (.leaf (22)) (.leaf (24))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (59)) (.branch 32 (.leaf (25)) (.leaf (41)))) (.branch 35 (.branch 34 (.leaf (26)) (.leaf (27))) (.branch 36 (.leaf (46)) (.leaf (28))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (36)) (.leaf (29))) (.branch 40 (.leaf (30)) (.leaf (52)))) (.branch 43 (.branch 42 (.leaf (31)) (.leaf (51))) (.branch 44 (.leaf (33)) (.leaf (49)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (34)) (.branch 47 (.leaf (35)) (.leaf (48)))) (.branch 50 (.branch 49 (.leaf (45)) (.leaf (38))) (.branch 51 (.leaf (43)) (.leaf (39))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (40)) (.leaf (42))) (.branch 55 (.leaf (58)) (.leaf (57)))) (.branch 58 (.branch 57 (.leaf (47)) (.leaf (55))) (.branch 59 (.leaf (54)) (.leaf (53))))))))
noncomputable def Ti (p : Fin 60) : Fin 60 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 60) : Fin 60 := T (S p)
theorem quotient_relations : (∀ p : Fin 60, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 60, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 60, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 60, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 60)) := [[0,3,9],[1,2,6],[4,5,10],[7,8,17],[11,12,23],[13,14,18],[15,16,26],[19,20,29],[21,22,34],[24,25,39],[27,28,46],[30,31,52],[32,33,53],[35,36,56],[37,38,47],[40,41,59],[42,43,58],[44,45,57],[48,49,55],[50,51,54]]
noncomputable def verticesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (6))) (.branch 6 (.leaf (7)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (9)) (.leaf (10))) (.branch 10 (.leaf (2)) (.leaf (8)))) (.branch 13 (.branch 12 (.leaf (12)) (.leaf (13))) (.branch 14 (.leaf (15)) (.leaf (16)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (18)) (.branch 17 (.leaf (19)) (.leaf (11)))) (.branch 20 (.branch 19 (.leaf (17)) (.leaf (21))) (.branch 21 (.leaf (22)) (.leaf (24))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (25)) (.leaf (14))) (.branch 25 (.leaf (27)) (.leaf (28)))) (.branch 28 (.branch 27 (.leaf (20)) (.leaf (30))) (.branch 29 (.leaf (31)) (.leaf (23))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (33)) (.branch 32 (.leaf (34)) (.leaf (36)))) (.branch 35 (.branch 34 (.leaf (37)) (.leaf (26))) (.branch 36 (.leaf (39)) (.leaf (40))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (42)) (.leaf (43))) (.branch 40 (.leaf (29)) (.leaf (45)))) (.branch 43 (.branch 42 (.leaf (46)) (.leaf (48))) (.branch 44 (.leaf (49)) (.leaf (51)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (52)) (.branch 47 (.leaf (32)) (.leaf (44)))) (.branch 50 (.branch 49 (.leaf (54)) (.leaf (55))) (.branch 51 (.leaf (57)) (.leaf (58))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (35)) (.leaf (38))) (.branch 55 (.leaf (59)) (.leaf (56)))) (.branch 58 (.branch 57 (.leaf (41)) (.leaf (53))) (.branch 59 (.leaf (50)) (.leaf (47))))))))
noncomputable def verticesIndex (p : Fin 60) : Fin 60 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (9)))) (.branch 5 (.branch 4 (.leaf (1)) (.leaf (2))) (.branch 6 (.leaf (6)) (.leaf (4))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (5)) (.leaf (10))) (.branch 10 (.leaf (7)) (.leaf (8)))) (.branch 13 (.branch 12 (.leaf (17)) (.leaf (11))) (.branch 14 (.leaf (12)) (.leaf (23)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (13)) (.branch 17 (.leaf (14)) (.leaf (18)))) (.branch 20 (.branch 19 (.leaf (15)) (.leaf (16))) (.branch 21 (.leaf (26)) (.leaf (19))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (20)) (.leaf (29))) (.branch 25 (.leaf (21)) (.leaf (22)))) (.branch 28 (.branch 27 (.leaf (34)) (.leaf (24))) (.branch 29 (.leaf (25)) (.leaf (39))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (28)) (.leaf (46)))) (.branch 35 (.branch 34 (.leaf (30)) (.leaf (31))) (.branch 36 (.leaf (52)) (.leaf (32))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (33)) (.leaf (53))) (.branch 40 (.leaf (35)) (.leaf (36)))) (.branch 43 (.branch 42 (.leaf (56)) (.leaf (37))) (.branch 44 (.leaf (38)) (.leaf (47)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (40)) (.branch 47 (.leaf (41)) (.leaf (59)))) (.branch 50 (.branch 49 (.leaf (42)) (.leaf (43))) (.branch 51 (.leaf (58)) (.leaf (44))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (45)) (.leaf (57))) (.branch 55 (.leaf (48)) (.leaf (49)))) (.branch 58 (.branch 57 (.leaf (55)) (.leaf (50))) (.branch 59 (.leaf (51)) (.leaf (54))))))))
noncomputable def verticesBack (p : Fin 60) : Fin 60 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 60, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 60 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 60, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 60)) := [[0,1],[2,4],[3,6],[5,7],[8,11],[9,13],[10,15],[12,18],[14,19],[16,21],[17,23],[20,24],[22,27],[25,30],[26,32],[28,35],[29,37],[31,40],[33,42],[34,44],[36,47],[38,48],[39,50],[41,53],[43,54],[45,55],[46,56],[49,57],[51,58],[52,59]]
noncomputable def edgesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (8))) (.branch 10 (.leaf (10)) (.leaf (12)))) (.branch 13 (.branch 12 (.leaf (9)) (.leaf (14))) (.branch 14 (.leaf (11)) (.leaf (16)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (13)) (.branch 17 (.leaf (18)) (.leaf (20)))) (.branch 20 (.branch 19 (.leaf (15)) (.leaf (17))) (.branch 21 (.leaf (22)) (.leaf (19))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (24)) (.leaf (21))) (.branch 25 (.leaf (23)) (.leaf (26)))) (.branch 28 (.branch 27 (.leaf (28)) (.leaf (25))) (.branch 29 (.leaf (30)) (.leaf (32))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (27)) (.branch 32 (.leaf (34)) (.leaf (29)))) (.branch 35 (.branch 34 (.leaf (36)) (.leaf (38))) (.branch 36 (.leaf (31)) (.leaf (40))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (33)) (.leaf (42))) (.branch 40 (.leaf (44)) (.leaf (35)))) (.branch 43 (.branch 42 (.leaf (46)) (.leaf (37))) (.branch 44 (.leaf (48)) (.leaf (39)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (50)) (.branch 47 (.leaf (52)) (.leaf (41)))) (.branch 50 (.branch 49 (.leaf (43)) (.leaf (54))) (.branch 51 (.leaf (45)) (.leaf (56))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (58)) (.leaf (47))) (.branch 55 (.leaf (49)) (.leaf (51)))) (.branch 58 (.branch 57 (.leaf (53)) (.leaf (55))) (.branch 59 (.leaf (57)) (.leaf (59))))))))
noncomputable def edgesIndex (p : Fin 60) : Fin 60 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 5 (.branch 4 (.leaf (4)) (.leaf (3))) (.branch 6 (.leaf (6)) (.leaf (5))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (7)) (.leaf (8))) (.branch 10 (.leaf (11)) (.leaf (9)))) (.branch 13 (.branch 12 (.leaf (13)) (.leaf (10))) (.branch 14 (.leaf (15)) (.leaf (12)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (18)) (.branch 17 (.leaf (14)) (.leaf (19)))) (.branch 20 (.branch 19 (.leaf (16)) (.leaf (21))) (.branch 21 (.leaf (17)) (.leaf (23))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (20)) (.leaf (24))) (.branch 25 (.leaf (22)) (.leaf (27)))) (.branch 28 (.branch 27 (.leaf (25)) (.leaf (30))) (.branch 29 (.leaf (26)) (.leaf (32))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (28)) (.branch 32 (.leaf (35)) (.leaf (29)))) (.branch 35 (.branch 34 (.leaf (37)) (.leaf (31))) (.branch 36 (.leaf (40)) (.leaf (33))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (42)) (.leaf (34))) (.branch 40 (.leaf (44)) (.leaf (36)))) (.branch 43 (.branch 42 (.leaf (47)) (.leaf (38))) (.branch 44 (.leaf (48)) (.leaf (39)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (50)) (.branch 47 (.leaf (41)) (.leaf (53)))) (.branch 50 (.branch 49 (.leaf (43)) (.leaf (54))) (.branch 51 (.leaf (45)) (.leaf (55))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (46)) (.leaf (56))) (.branch 55 (.leaf (49)) (.leaf (57)))) (.branch 58 (.branch 57 (.leaf (51)) (.leaf (58))) (.branch 59 (.leaf (52)) (.leaf (59))))))))
noncomputable def edgesBack (p : Fin 60) : Fin 60 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 60, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 60 := by decide +kernel
theorem edges_partition : ∀ p : Fin 60, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 60)) := [[0,2,5,8,12,13],[1,3],[4,6,9,14,20,25,31,41,32,15],[7,10,16,22,28,36,37,19,18,23],[11,17],[21,26,33,43,50,24,29,38,49,44],[27,34,45,48,47,56],[30,39,51,42,53,59],[35,46],[40,52],[54,58],[55,57]]
noncomputable def facesIndexData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (6)) (.leaf (1)))) (.branch 5 (.branch 4 (.leaf (7)) (.leaf (8))) (.branch 6 (.leaf (2)) (.leaf (9))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (18)) (.leaf (3))) (.branch 10 (.leaf (10)) (.leaf (19)))) (.branch 13 (.branch 12 (.leaf (28)) (.leaf (4))) (.branch 14 (.leaf (5)) (.leaf (11)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (17)) (.branch 17 (.leaf (20)) (.leaf (29)))) (.branch 20 (.branch 19 (.leaf (26)) (.leaf (25))) (.branch 21 (.leaf (12)) (.leaf (30))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (21)) (.leaf (27))) (.branch 25 (.leaf (35)) (.leaf (13)))) (.branch 28 (.branch 27 (.leaf (31)) (.leaf (40))) (.branch 29 (.leaf (22)) (.leaf (36))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (46)) (.branch 32 (.leaf (14)) (.leaf (16)))) (.branch 35 (.branch 34 (.leaf (32)) (.leaf (41))) (.branch 36 (.leaf (52)) (.leaf (23))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (24)) (.leaf (37))) (.branch 40 (.leaf (47)) (.leaf (54)))) (.branch 43 (.branch 42 (.leaf (15)) (.leaf (49))) (.branch 44 (.leaf (33)) (.leaf (39)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (42)) (.branch 47 (.leaf (53)) (.leaf (44)))) (.branch 50 (.branch 49 (.leaf (43)) (.leaf (38))) (.branch 51 (.leaf (34)) (.leaf (48))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (55)) (.leaf (50))) (.branch 55 (.leaf (56)) (.leaf (58)))) (.branch 58 (.branch 57 (.leaf (45)) (.leaf (59))) (.branch 59 (.leaf (57)) (.leaf (51))))))))
noncomputable def facesIndex (p : Fin 60) : Fin 60 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 60) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 5 (.branch 4 (.leaf (8)) (.leaf (12))) (.branch 6 (.leaf (13)) (.leaf (1))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (3)) (.leaf (4))) (.branch 10 (.leaf (6)) (.leaf (9)))) (.branch 13 (.branch 12 (.leaf (14)) (.leaf (20))) (.branch 14 (.leaf (25)) (.leaf (31)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (41)) (.branch 17 (.leaf (32)) (.leaf (15)))) (.branch 20 (.branch 19 (.leaf (7)) (.leaf (10))) (.branch 21 (.leaf (16)) (.leaf (22))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (28)) (.leaf (36))) (.branch 25 (.leaf (37)) (.leaf (19)))) (.branch 28 (.branch 27 (.leaf (18)) (.leaf (23))) (.branch 29 (.leaf (11)) (.leaf (17))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (21)) (.branch 32 (.leaf (26)) (.leaf (33)))) (.branch 35 (.branch 34 (.leaf (43)) (.leaf (50))) (.branch 36 (.leaf (24)) (.leaf (29))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (38)) (.leaf (49))) (.branch 40 (.leaf (44)) (.leaf (27)))) (.branch 43 (.branch 42 (.leaf (34)) (.leaf (45))) (.branch 44 (.leaf (48)) (.leaf (47)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (56)) (.branch 47 (.leaf (30)) (.leaf (39)))) (.branch 50 (.branch 49 (.leaf (51)) (.leaf (42))) (.branch 51 (.leaf (53)) (.leaf (59))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (35)) (.leaf (46))) (.branch 55 (.leaf (40)) (.leaf (52)))) (.branch 58 (.branch 57 (.leaf (54)) (.leaf (58))) (.branch 59 (.leaf (55)) (.leaf (57))))))))
noncomputable def facesBack (p : Fin 60) : Fin 60 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 60, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 60 := by decide +kernel
theorem faces_partition : ∀ p : Fin 60, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [6,2,10,10,2,10,6,6,2,2,2,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 20 - 30 + 12 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 30 (.branch 15 (.branch 7 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 5 (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.leaf (⟨-1,1,-1,0⟩))) (.branch 6 (.leaf (⟨1,2,0,1⟩)) (.leaf (⟨-1,0,-1,-1⟩))))) (.branch 11 (.branch 9 (.branch 8 (.leaf (⟨2,-1,1,0⟩)) (.leaf (⟨-1,-3,0,-1⟩))) (.branch 10 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨2,1,1,1⟩)))) (.branch 13 (.branch 12 (.leaf (⟨-3,1,-1,0⟩)) (.leaf (⟨1,4,0,1⟩))) (.branch 14 (.leaf (⟨-1,-5,0,-1⟩)) (.leaf (⟨-5,-4,-1,-1⟩)))))) (.branch 22 (.branch 18 (.branch 16 (.leaf (⟨1,-2,1,-1⟩)) (.branch 17 (.leaf (⟨-2,-3,-1,-2⟩)) (.leaf (⟨-3,-2,-1,-1⟩)))) (.branch 20 (.branch 19 (.leaf (⟨4,-1,1,0⟩)) (.leaf (⟨-4,5,-1,1⟩))) (.branch 21 (.leaf (⟨5,9,1,2⟩)) (.leaf (⟨-3,2,-2,1⟩))))) (.branch 26 (.branch 24 (.branch 23 (.leaf (⟨2,5,1,3⟩)) (.leaf (⟨4,3,1,1⟩))) (.branch 25 (.leaf (⟨9,-5,2,-1⟩)) (.leaf (⟨-5,-14,-1,-3⟩)))) (.branch 28 (.branch 27 (.leaf (⟨-3,-1,-2,-1⟩)) (.leaf (⟨5,-2,3,-1⟩))) (.branch 29 (.leaf (⟨-2,-7,-1,-4⟩)) (.leaf (⟨9,4,2,1⟩))))))) (.branch 45 (.branch 37 (.branch 33 (.branch 31 (.leaf (⟨-14,5,-3,1⟩)) (.branch 32 (.leaf (⟨5,19,1,4⟩)) (.leaf (⟨-1,3,-1,2⟩)))) (.branch 35 (.branch 34 (.leaf (⟨3,4,2,3⟩)) (.leaf (⟨5,3,3,2⟩))) (.branch 36 (.leaf (⟨17,4,4,1⟩)) (.leaf (⟨-4,13,-1,3⟩))))) (.branch 41 (.branch 39 (.branch 38 (.leaf (⟨4,-9,1,-2⟩)) (.leaf (⟨-9,-13,-2,-3⟩))) (.branch 40 (.leaf (⟨-14,-9,-3,-2⟩)) (.leaf (⟨-5,-1,-4,-1⟩)))) (.branch 43 (.branch 42 (.leaf (⟨1,-4,1,-3⟩)) (.leaf (⟨4,-3,3,-2⟩))) (.branch 44 (.leaf (⟨-3,-7,-2,-5⟩)) (.leaf (⟨3,-5,2,-3⟩)))))) (.branch 52 (.branch 48 (.branch 46 (.leaf (⟨-5,-8,-3,-5⟩)) (.branch 47 (.leaf (⟨-7,-5,-4,-3⟩)) (.leaf (⟨-13,-4,-3,-1⟩)))) (.branch 50 (.branch 49 (.leaf (⟨-13,9,-3,2⟩)) (.leaf (⟨9,22,2,5⟩))) (.branch 51 (.leaf (⟨-9,14,-2,3⟩)) (.leaf (⟨14,23,3,5⟩))))) (.branch 56 (.branch 54 (.branch 53 (.leaf (⟨19,14,4,3⟩)) (.leaf (⟨4,1,3,1⟩))) (.branch 55 (.leaf (⟨23,9,5,2⟩)) (.leaf (⟨22,13,5,3⟩)))) (.branch 58 (.branch 57 (.leaf (⟨13,17,3,4⟩)) (.leaf (⟨-8,-3,-5,-2⟩))) (.branch 59 (.leaf (⟨-7,-4,-5,-3⟩)) (.leaf (⟨-4,-5,-3,-4⟩))))))))
noncomputable def liftMatrix (p : Fin 60) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 60) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],6⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],7⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],10⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],11⟩,⟨⟨1,4,0,1⟩,[.t (4)],12⟩,⟨⟨-1,-5,0,-1⟩,[.t (5)],13⟩,⟨⟨-5,-4,-1,-1⟩,[.t (5),.s,.t (1)],14⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],15⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],16⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],17⟩,⟨⟨4,-1,1,0⟩,[.t (4),.s,.t (0)],18⟩,⟨⟨-4,5,-1,1⟩,[.t (4),.s,.t (-1)],19⟩,⟨⟨5,9,1,2⟩,[.t (5),.s,.t (2)],20⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],21⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],22⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],23⟩,⟨⟨9,-5,2,-1⟩,[.t (4),.s,.t (-2),.s,.t (-1)],24⟩,⟨⟨-5,-14,-1,-3⟩,[.t (5),.s,.t (3)],25⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],26⟩,⟨⟨5,-2,3,-1⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],27⟩,⟨⟨-2,-7,-1,-4⟩,[.t (2),.s,.t (4)],28⟩,⟨⟨9,4,2,1⟩,[.t (4),.s,.t (-2),.s,.t (0)],29⟩,⟨⟨-14,5,-3,1⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (-1)],30⟩,⟨⟨5,19,1,4⟩,[.t (5),.s,.t (4)],31⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],32⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],33⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],34⟩,⟨⟨17,4,4,1⟩,[.t (4),.s,.t (-4),.s,.t (0)],35⟩,⟨⟨-4,13,-1,3⟩,[.t (4),.s,.t (-3)],36⟩,⟨⟨4,-9,1,-2⟩,[.t (4),.s,.t (-2)],37⟩,⟨⟨-9,-13,-2,-3⟩,[.t (4),.s,.t (-2),.s,.t (1)],38⟩,⟨⟨-14,-9,-3,-2⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (0)],39⟩,⟨⟨-5,-1,-4,-1⟩,[.t (1),.s,.t (-4),.s,.t (0)],40⟩,⟨⟨1,-4,1,-3⟩,[.t (1),.s,.t (-3)],41⟩,⟨⟨4,-3,3,-2⟩,[.t (1),.s,.t (-3),.s,.t (-1)],42⟩,⟨⟨-3,-7,-2,-5⟩,[.t (1),.s,.t (-2),.s,.t (2)],43⟩,⟨⟨3,-5,2,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2)],44⟩,⟨⟨-5,-8,-3,-5⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (1)],45⟩,⟨⟨-7,-5,-4,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],46⟩,⟨⟨-13,-4,-3,-1⟩,[.t (4),.s,.t (-3),.s,.t (0)],47⟩,⟨⟨-13,9,-3,2⟩,[.t (4),.s,.t (-3),.s,.t (-1)],48⟩,⟨⟨9,22,2,5⟩,[.t (4),.s,.t (-2),.s,.t (2)],49⟩,⟨⟨-9,14,-2,3⟩,[.t (4),.s,.t (-2),.s,.t (-2)],50⟩,⟨⟨14,23,3,5⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (1)],51⟩,⟨⟨19,14,4,3⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],52⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],53⟩,⟨⟨23,9,5,2⟩,[.t (4),.s,.t (-2),.s,.t (-3),.s,.t (0)],54⟩,⟨⟨22,13,5,3⟩,[.t (4),.s,.t (-3),.s,.t (-2),.s,.t (0)],55⟩,⟨⟨13,17,3,4⟩,[.t (4),.s,.t (-3),.s,.t (1)],56⟩,⟨⟨-8,-3,-5,-2⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (0)],57⟩,⟨⟨-7,-4,-5,-3⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (0)],58⟩,⟨⟨-4,-5,-3,-4⟩,[.t (1),.s,.t (-3),.s,.t (1)],59⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 60 ∧ ((List.finRange 60).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 60) := [⟨9,2,⟨⟨-1,-6,0,-1⟩,[.t (6)],0⟩⟩,⟨3,1,⟨⟨-1,0,-2,-1⟩,[.t (0),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨6,1,⟨⟨-1,0,2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨40,5,⟨⟨39,-44,8,-9⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨59,11,⟨⟨113,-146,24,-31⟩,[.t (4),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨58,10,⟨⟨139,-190,30,-41⟩,[.t (4),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨43,6,⟨⟨-91,132,-20,29⟩,[.t (4),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨57,9,⟨⟨89,-138,20,-31⟩,[.t (4),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨45,7,⟨⟨-131,214,-30,49⟩,[.t (4),.s,.t (-3),.s,.t (-4),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨46,8,⟨⟨-103,176,-24,41⟩,[.t (4),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-2)],0⟩⟩,⟨28,4,⟨⟨-33,62,-8,15⟩,[.t (4),.s,.t (-8),.s,.t (-2)],0⟩⟩,⟨17,3,⟨⟨-7,18,-2,5⟩,[.t (3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨23,3,⟨⟨5,-18,2,-7⟩,[.t (2),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨35,4,⟨⟨15,-62,8,-33⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨56,8,⟨⟨41,-176,24,-103⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨55,7,⟨⟨49,-214,30,-131⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨49,9,⟨⟨-31,138,-20,89⟩,[.t (1),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-5)],0⟩⟩,⟨54,6,⟨⟨29,-132,20,-91⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-5)],0⟩⟩,⟨51,10,⟨⟨-41,190,-30,139⟩,[.t (1),.s,.t (-3),.s,.t (-4),.s,.t (-3),.s,.t (-5)],0⟩⟩,⟨52,11,⟨⟨-31,146,-24,113⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-5)],0⟩⟩,⟨31,5,⟨⟨-9,44,-8,39⟩,[.t (1),.s,.t (-8),.s,.t (-5)],0⟩⟩,⟨13,2,⟨⟨-1,6,0,-1⟩,[.t (-6)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(0,1),(1,1),(5,4),(4,3),(7,5),(3,2),(8,5),(5,3),(7,4),(2,1),(3,1),(4,1),(17,4),(13,3),(22,5),(9,2),(23,5),(14,3),(19,4),(5,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G240_190_c1

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
