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
namespace G240_89_c0
noncomputable def originalSData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (13)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (16))) (.branch 12 (.leaf (17)) (.leaf (7)))) (.branch 15 (.branch 14 (.leaf (8)) (.leaf (20))) (.branch 16 (.leaf (22)) (.branch 17 (.leaf (10)) (.leaf (11))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (25)) (.leaf (27))) (.branch 21 (.leaf (14)) (.leaf (29)))) (.branch 24 (.branch 23 (.leaf (15)) (.leaf (31))) (.branch 25 (.leaf (33)) (.branch 26 (.leaf (18)) (.leaf (35)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (19)) (.leaf (37))) (.branch 30 (.leaf (21)) (.leaf (40)))) (.branch 33 (.branch 32 (.leaf (23)) (.leaf (43))) (.branch 34 (.leaf (24)) (.branch 35 (.leaf (45)) (.leaf (26)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (48)) (.leaf (28))) (.branch 39 (.leaf (51)) (.leaf (53)))) (.branch 42 (.branch 41 (.leaf (30)) (.leaf (56))) (.branch 43 (.leaf (57)) (.branch 44 (.leaf (32)) (.leaf (60)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (34)) (.leaf (54))) (.branch 48 (.leaf (59)) (.leaf (36)))) (.branch 51 (.branch 50 (.leaf (52)) (.leaf (65))) (.branch 52 (.leaf (38)) (.branch 53 (.leaf (49)) (.leaf (39))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (46)) (.leaf (63))) (.branch 57 (.leaf (41)) (.leaf (42)))) (.branch 60 (.branch 59 (.leaf (64)) (.leaf (47))) (.branch 61 (.leaf (44)) (.branch 62 (.leaf (66)) (.leaf (71)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (55)) (.leaf (58))) (.branch 66 (.leaf (50)) (.leaf (61)))) (.branch 69 (.branch 68 (.leaf (69)) (.leaf (70))) (.branch 70 (.leaf (67)) (.branch 71 (.leaf (68)) (.leaf (62)))))))))
noncomputable def originalS (p : Fin 72) : Fin 72 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (10))) (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (14)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (15)) (.leaf (17))) (.branch 12 (.leaf (18)) (.leaf (19)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (21))) (.branch 16 (.leaf (23)) (.branch 17 (.leaf (24)) (.leaf (0))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (26)) (.leaf (28))) (.branch 21 (.leaf (12)) (.leaf (30)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (32))) (.branch 25 (.leaf (34)) (.branch 26 (.leaf (16)) (.leaf (36)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (38))) (.branch 30 (.leaf (39)) (.leaf (41)))) (.branch 33 (.branch 32 (.leaf (42)) (.leaf (44))) (.branch 34 (.leaf (9)) (.branch 35 (.leaf (46)) (.leaf (47)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (49)) (.leaf (50))) (.branch 39 (.leaf (52)) (.leaf (54)))) (.branch 42 (.branch 41 (.leaf (55)) (.leaf (57))) (.branch 43 (.leaf (58)) (.branch 44 (.leaf (59)) (.leaf (61)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (62)) (.leaf (63))) (.branch 48 (.leaf (31)) (.leaf (64)))) (.branch 51 (.branch 50 (.leaf (65)) (.leaf (51))) (.branch 52 (.leaf (66)) (.branch 53 (.leaf (67)) (.leaf (20))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (68)) (.leaf (53))) (.branch 57 (.leaf (69)) (.leaf (22)))) (.branch 60 (.branch 59 (.leaf (35)) (.leaf (25))) (.branch 61 (.leaf (70)) (.branch 62 (.leaf (37)) (.leaf (60)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (29)) (.leaf (56))) (.branch 66 (.leaf (27)) (.leaf (71)))) (.branch 69 (.branch 68 (.leaf (40)) (.leaf (43))) (.branch 70 (.leaf (48)) (.branch 71 (.leaf (45)) (.leaf (33)))))))))
noncomputable def originalT (p : Fin 72) : Fin 72 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (5))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (8)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (9)) (.leaf (10))) (.branch 12 (.leaf (11)) (.leaf (12)))) (.branch 15 (.branch 14 (.leaf (13)) (.leaf (14))) (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (17))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (18)) (.leaf (19))) (.branch 21 (.leaf (20)) (.leaf (21)))) (.branch 24 (.branch 23 (.leaf (22)) (.leaf (23))) (.branch 25 (.leaf (24)) (.branch 26 (.leaf (25)) (.leaf (26)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (27)) (.leaf (28))) (.branch 30 (.leaf (29)) (.leaf (30)))) (.branch 33 (.branch 32 (.leaf (31)) (.leaf (32))) (.branch 34 (.leaf (33)) (.branch 35 (.leaf (34)) (.leaf (35)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (36)) (.leaf (37))) (.branch 39 (.leaf (38)) (.leaf (39)))) (.branch 42 (.branch 41 (.leaf (40)) (.leaf (41))) (.branch 43 (.leaf (42)) (.branch 44 (.leaf (43)) (.leaf (44)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (45)) (.leaf (46))) (.branch 48 (.leaf (47)) (.leaf (48)))) (.branch 51 (.branch 50 (.leaf (49)) (.leaf (50))) (.branch 52 (.leaf (51)) (.branch 53 (.leaf (52)) (.leaf (53))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (54)) (.leaf (55))) (.branch 57 (.leaf (56)) (.leaf (57)))) (.branch 60 (.branch 59 (.leaf (58)) (.leaf (59))) (.branch 61 (.leaf (60)) (.branch 62 (.leaf (61)) (.leaf (62)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (63)) (.leaf (64))) (.branch 66 (.leaf (65)) (.leaf (66)))) (.branch 69 (.branch 68 (.leaf (67)) (.leaf (68))) (.branch 70 (.leaf (69)) (.branch 71 (.leaf (70)) (.leaf (71)))))))))
noncomputable def projection (p : Fin 72) : Fin 72 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (4)) (.leaf (5))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (7)) (.leaf (8)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (9)) (.leaf (10))) (.branch 12 (.leaf (11)) (.leaf (12)))) (.branch 15 (.branch 14 (.leaf (13)) (.leaf (14))) (.branch 16 (.leaf (15)) (.branch 17 (.leaf (16)) (.leaf (17))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (18)) (.leaf (19))) (.branch 21 (.leaf (20)) (.leaf (21)))) (.branch 24 (.branch 23 (.leaf (22)) (.leaf (23))) (.branch 25 (.leaf (24)) (.branch 26 (.leaf (25)) (.leaf (26)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (27)) (.leaf (28))) (.branch 30 (.leaf (29)) (.leaf (30)))) (.branch 33 (.branch 32 (.leaf (31)) (.leaf (32))) (.branch 34 (.leaf (33)) (.branch 35 (.leaf (34)) (.leaf (35)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (36)) (.leaf (37))) (.branch 39 (.leaf (38)) (.leaf (39)))) (.branch 42 (.branch 41 (.leaf (40)) (.leaf (41))) (.branch 43 (.leaf (42)) (.branch 44 (.leaf (43)) (.leaf (44)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (45)) (.leaf (46))) (.branch 48 (.leaf (47)) (.leaf (48)))) (.branch 51 (.branch 50 (.leaf (49)) (.leaf (50))) (.branch 52 (.leaf (51)) (.branch 53 (.leaf (52)) (.leaf (53))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (54)) (.leaf (55))) (.branch 57 (.leaf (56)) (.leaf (57)))) (.branch 60 (.branch 59 (.leaf (58)) (.leaf (59))) (.branch 61 (.leaf (60)) (.branch 62 (.leaf (61)) (.leaf (62)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (63)) (.leaf (64))) (.branch 66 (.leaf (65)) (.leaf (66)))) (.branch 69 (.branch 68 (.leaf (67)) (.leaf (68))) (.branch 70 (.leaf (69)) (.branch 71 (.leaf (70)) (.leaf (71)))))))))
noncomputable def representative (p : Fin 72) : Fin 72 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (13)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (16))) (.branch 12 (.leaf (17)) (.leaf (7)))) (.branch 15 (.branch 14 (.leaf (8)) (.leaf (20))) (.branch 16 (.leaf (22)) (.branch 17 (.leaf (10)) (.leaf (11))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (25)) (.leaf (27))) (.branch 21 (.leaf (14)) (.leaf (29)))) (.branch 24 (.branch 23 (.leaf (15)) (.leaf (31))) (.branch 25 (.leaf (33)) (.branch 26 (.leaf (18)) (.leaf (35)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (19)) (.leaf (37))) (.branch 30 (.leaf (21)) (.leaf (40)))) (.branch 33 (.branch 32 (.leaf (23)) (.leaf (43))) (.branch 34 (.leaf (24)) (.branch 35 (.leaf (45)) (.leaf (26)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (48)) (.leaf (28))) (.branch 39 (.leaf (51)) (.leaf (53)))) (.branch 42 (.branch 41 (.leaf (30)) (.leaf (56))) (.branch 43 (.leaf (57)) (.branch 44 (.leaf (32)) (.leaf (60)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (34)) (.leaf (54))) (.branch 48 (.leaf (59)) (.leaf (36)))) (.branch 51 (.branch 50 (.leaf (52)) (.leaf (65))) (.branch 52 (.leaf (38)) (.branch 53 (.leaf (49)) (.leaf (39))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (46)) (.leaf (63))) (.branch 57 (.leaf (41)) (.leaf (42)))) (.branch 60 (.branch 59 (.leaf (64)) (.leaf (47))) (.branch 61 (.leaf (44)) (.branch 62 (.leaf (66)) (.leaf (71)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (55)) (.leaf (58))) (.branch 66 (.leaf (50)) (.leaf (61)))) (.branch 69 (.branch 68 (.leaf (69)) (.leaf (70))) (.branch 70 (.leaf (67)) (.branch 71 (.leaf (68)) (.leaf (62)))))))))
noncomputable def S (p : Fin 72) : Fin 72 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (10))) (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (14)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (15)) (.leaf (17))) (.branch 12 (.leaf (18)) (.leaf (19)))) (.branch 15 (.branch 14 (.leaf (1)) (.leaf (21))) (.branch 16 (.leaf (23)) (.branch 17 (.leaf (24)) (.leaf (0))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (26)) (.leaf (28))) (.branch 21 (.leaf (12)) (.leaf (30)))) (.branch 24 (.branch 23 (.leaf (4)) (.leaf (32))) (.branch 25 (.leaf (34)) (.branch 26 (.leaf (16)) (.leaf (36)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (38))) (.branch 30 (.leaf (39)) (.leaf (41)))) (.branch 33 (.branch 32 (.leaf (42)) (.leaf (44))) (.branch 34 (.leaf (9)) (.branch 35 (.leaf (46)) (.leaf (47)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (49)) (.leaf (50))) (.branch 39 (.leaf (52)) (.leaf (54)))) (.branch 42 (.branch 41 (.leaf (55)) (.leaf (57))) (.branch 43 (.leaf (58)) (.branch 44 (.leaf (59)) (.leaf (61)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (62)) (.leaf (63))) (.branch 48 (.leaf (31)) (.leaf (64)))) (.branch 51 (.branch 50 (.leaf (65)) (.leaf (51))) (.branch 52 (.leaf (66)) (.branch 53 (.leaf (67)) (.leaf (20))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (68)) (.leaf (53))) (.branch 57 (.leaf (69)) (.leaf (22)))) (.branch 60 (.branch 59 (.leaf (35)) (.leaf (25))) (.branch 61 (.leaf (70)) (.branch 62 (.leaf (37)) (.leaf (60)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (29)) (.leaf (56))) (.branch 66 (.leaf (27)) (.leaf (71)))) (.branch 69 (.branch 68 (.leaf (40)) (.leaf (43))) (.branch 70 (.leaf (48)) (.branch 71 (.leaf (45)) (.leaf (33)))))))))
noncomputable def T (p : Fin 72) : Fin 72 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (17)) (.leaf (13))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (22)) (.leaf (2))) (.branch 7 (.leaf (27)) (.branch 8 (.leaf (3)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (33)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (20)))) (.branch 15 (.branch 14 (.leaf (7)) (.leaf (8))) (.branch 16 (.leaf (9)) (.branch 17 (.leaf (25)) (.leaf (10))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (11)) (.leaf (12))) (.branch 21 (.leaf (53)) (.leaf (14)))) (.branch 24 (.branch 23 (.leaf (57)) (.leaf (15))) (.branch 25 (.leaf (16)) (.branch 26 (.leaf (59)) (.leaf (18)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (65)) (.leaf (19))) (.branch 30 (.leaf (63)) (.leaf (21)))) (.branch 33 (.branch 32 (.leaf (47)) (.leaf (23))) (.branch 34 (.leaf (71)) (.branch 35 (.leaf (24)) (.leaf (58)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (26)) (.leaf (61))) (.branch 39 (.leaf (28)) (.leaf (29)))) (.branch 42 (.branch 41 (.leaf (67)) (.leaf (30))) (.branch 43 (.leaf (31)) (.branch 44 (.leaf (68)) (.leaf (32)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (70)) (.leaf (34))) (.branch 48 (.leaf (35)) (.leaf (69)))) (.branch 51 (.branch 50 (.leaf (36)) (.leaf (37))) (.branch 52 (.leaf (50)) (.branch 53 (.leaf (38)) (.leaf (55))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (39)) (.leaf (40))) (.branch 57 (.leaf (64)) (.leaf (41)))) (.branch 60 (.branch 59 (.leaf (42)) (.leaf (43))) (.branch 61 (.leaf (62)) (.branch 62 (.leaf (44)) (.leaf (45)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (46)) (.leaf (48))) (.branch 66 (.leaf (49)) (.leaf (51)))) (.branch 69 (.branch 68 (.leaf (52)) (.leaf (54))) (.branch 70 (.leaf (56)) (.branch 71 (.leaf (60)) (.leaf (66)))))))))
noncomputable def Ti (p : Fin 72) : Fin 72 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 72) : Fin 72 := T (S p)
theorem quotient_relations : (∀ p : Fin 72, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 72, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 72, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 72, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 72)) := [[0,3,11],[1,2,8],[4,5,15],[6,7,19],[9,10,24],[12,13,14],[16,17,18],[20,21,39],[22,23,42],[25,26,47],[27,28,50],[29,30,55],[31,32,59],[33,34,62],[35,36,64],[37,38,66],[40,41,69],[43,44,70],[45,46,68],[48,49,67],[51,52,65],[53,54,63],[56,57,58],[60,61,71]]
noncomputable def verticesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (2)) (.leaf (15)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (17))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (18)) (.leaf (19))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (20)) (.leaf (11))) (.branch 21 (.leaf (21)) (.leaf (22)))) (.branch 24 (.branch 23 (.leaf (24)) (.leaf (25))) (.branch 25 (.leaf (14)) (.branch 26 (.leaf (27)) (.leaf (28)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (30)) (.leaf (31))) (.branch 30 (.leaf (33)) (.leaf (34)))) (.branch 33 (.branch 32 (.leaf (36)) (.leaf (37))) (.branch 34 (.leaf (39)) (.branch 35 (.leaf (40)) (.leaf (42)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (43)) (.leaf (45))) (.branch 39 (.leaf (46)) (.leaf (23)))) (.branch 42 (.branch 41 (.leaf (48)) (.leaf (49))) (.branch 43 (.leaf (26)) (.branch 44 (.leaf (51)) (.leaf (52)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (54)) (.leaf (55))) (.branch 48 (.leaf (29)) (.leaf (57)))) (.branch 51 (.branch 50 (.leaf (58)) (.leaf (32))) (.branch 52 (.leaf (60)) (.branch 53 (.leaf (61)) (.leaf (63))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (64)) (.leaf (35))) (.branch 57 (.leaf (66)) (.leaf (67)))) (.branch 60 (.branch 59 (.leaf (68)) (.leaf (38))) (.branch 61 (.leaf (69)) (.branch 62 (.leaf (70)) (.leaf (41)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (65)) (.leaf (44))) (.branch 66 (.leaf (62)) (.leaf (47)))) (.branch 69 (.branch 68 (.leaf (59)) (.leaf (56))) (.branch 70 (.leaf (50)) (.branch 71 (.leaf (53)) (.leaf (71)))))))))
noncomputable def verticesIndex (p : Fin 72) : Fin 72 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (11)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (15)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (19)) (.leaf (9)))) (.branch 15 (.branch 14 (.leaf (10)) (.leaf (24))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (14))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (16)) (.leaf (17))) (.branch 21 (.leaf (18)) (.leaf (20)))) (.branch 24 (.branch 23 (.leaf (21)) (.leaf (39))) (.branch 25 (.leaf (22)) (.branch 26 (.leaf (23)) (.leaf (42)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (25)) (.leaf (26))) (.branch 30 (.leaf (47)) (.leaf (27)))) (.branch 33 (.branch 32 (.leaf (28)) (.leaf (50))) (.branch 34 (.leaf (29)) (.branch 35 (.leaf (30)) (.leaf (55)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (31)) (.leaf (32))) (.branch 39 (.leaf (59)) (.leaf (33)))) (.branch 42 (.branch 41 (.leaf (34)) (.leaf (62))) (.branch 43 (.leaf (35)) (.branch 44 (.leaf (36)) (.leaf (64)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (37)) (.leaf (38))) (.branch 48 (.leaf (66)) (.leaf (40)))) (.branch 51 (.branch 50 (.leaf (41)) (.leaf (69))) (.branch 52 (.leaf (43)) (.branch 53 (.leaf (44)) (.leaf (70))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (45)) (.leaf (46))) (.branch 57 (.leaf (68)) (.leaf (48)))) (.branch 60 (.branch 59 (.leaf (49)) (.leaf (67))) (.branch 61 (.leaf (51)) (.branch 62 (.leaf (52)) (.leaf (65)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (53)) (.leaf (54))) (.branch 66 (.leaf (63)) (.leaf (56)))) (.branch 69 (.branch 68 (.leaf (57)) (.leaf (58))) (.branch 70 (.leaf (60)) (.branch 71 (.leaf (61)) (.leaf (71)))))))))
noncomputable def verticesBack (p : Fin 72) : Fin 72 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 72, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 72 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 72, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 72)) := [[0,1],[2,4],[3,6],[5,9],[7,12],[8,13],[10,16],[11,17],[14,20],[15,22],[18,25],[19,27],[21,29],[23,31],[24,33],[26,35],[28,37],[30,40],[32,43],[34,45],[36,48],[38,51],[39,53],[41,56],[42,57],[44,60],[46,54],[47,59],[49,52],[50,65],[55,63],[58,64],[61,66],[62,71],[67,69],[68,70]]
noncomputable def edgesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (10)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (7)) (.leaf (12))) (.branch 12 (.leaf (14)) (.leaf (9)))) (.branch 15 (.branch 14 (.leaf (11)) (.leaf (16))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (13)) (.leaf (15))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (20)) (.leaf (22))) (.branch 21 (.leaf (17)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (19)) (.leaf (26))) (.branch 25 (.leaf (28)) (.branch 26 (.leaf (21)) (.leaf (30)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (23)) (.leaf (32))) (.branch 30 (.leaf (25)) (.leaf (34)))) (.branch 33 (.branch 32 (.leaf (27)) (.leaf (36))) (.branch 34 (.leaf (29)) (.branch 35 (.leaf (38)) (.leaf (31)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (40)) (.leaf (33))) (.branch 39 (.leaf (42)) (.leaf (44)))) (.branch 42 (.branch 41 (.leaf (35)) (.leaf (46))) (.branch 43 (.leaf (48)) (.branch 44 (.leaf (37)) (.leaf (50)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (39)) (.leaf (52))) (.branch 48 (.leaf (54)) (.leaf (41)))) (.branch 51 (.branch 50 (.leaf (56)) (.leaf (58))) (.branch 52 (.leaf (43)) (.branch 53 (.leaf (57)) (.leaf (45))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (53)) (.leaf (60))) (.branch 57 (.leaf (47)) (.leaf (49)))) (.branch 60 (.branch 59 (.leaf (62)) (.leaf (55))) (.branch 61 (.leaf (51)) (.branch 62 (.leaf (64)) (.leaf (66)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (61)) (.leaf (63))) (.branch 66 (.leaf (59)) (.leaf (65)))) (.branch 69 (.branch 68 (.leaf (68)) (.leaf (70))) (.branch 70 (.leaf (69)) (.branch 71 (.leaf (71)) (.leaf (67)))))))))
noncomputable def edgesIndex (p : Fin 72) : Fin 72 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (12)) (.leaf (8))) (.branch 12 (.leaf (13)) (.leaf (10)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (11))) (.branch 16 (.leaf (17)) (.branch 17 (.leaf (14)) (.leaf (20))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (15)) (.leaf (22))) (.branch 21 (.leaf (18)) (.leaf (25)))) (.branch 24 (.branch 23 (.leaf (19)) (.leaf (27))) (.branch 25 (.leaf (21)) (.branch 26 (.leaf (29)) (.leaf (23)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (31)) (.leaf (24))) (.branch 30 (.leaf (33)) (.leaf (26)))) (.branch 33 (.branch 32 (.leaf (35)) (.leaf (28))) (.branch 34 (.leaf (37)) (.branch 35 (.leaf (30)) (.leaf (40)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (32)) (.leaf (43))) (.branch 39 (.leaf (34)) (.leaf (45)))) (.branch 42 (.branch 41 (.leaf (36)) (.leaf (48))) (.branch 43 (.leaf (38)) (.branch 44 (.leaf (51)) (.leaf (39)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (53)) (.leaf (41))) (.branch 48 (.leaf (56)) (.leaf (42)))) (.branch 51 (.branch 50 (.leaf (57)) (.leaf (44))) (.branch 52 (.leaf (60)) (.branch 53 (.leaf (46)) (.leaf (54))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (47)) (.leaf (59))) (.branch 57 (.leaf (49)) (.leaf (52)))) (.branch 60 (.branch 59 (.leaf (50)) (.leaf (65))) (.branch 61 (.leaf (55)) (.branch 62 (.leaf (63)) (.leaf (58)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (64)) (.leaf (61))) (.branch 66 (.leaf (66)) (.leaf (62)))) (.branch 69 (.branch 68 (.leaf (71)) (.leaf (67))) (.branch 70 (.leaf (69)) (.branch 71 (.leaf (68)) (.leaf (70)))))))))
noncomputable def edgesBack (p : Fin 72) : Fin 72 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 72, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 72 := by decide +kernel
theorem edges_partition : ∀ p : Fin 72, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 72)) := [[0,2,5,10,17],[1,3,7,13],[4,8,14,21,30,41,57,22],[6,11,18,26,36,49,65,27],[9,15,23,32,44,61,37,50,51,66,71,33],[12,19,28,38,52,67,40,55,53,20],[16,24,34,46,63,29,39,54,68,43,59,25],[31,42,58,35,47],[45,62,60,70],[48,64,56,69]]
noncomputable def facesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (5))) (.branch 3 (.leaf (1)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (2))) (.branch 7 (.leaf (17)) (.branch 8 (.leaf (7)) (.leaf (10)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (25)) (.leaf (3))) (.branch 12 (.leaf (18)) (.leaf (37)))) (.branch 15 (.branch 14 (.leaf (8)) (.leaf (11))) (.branch 16 (.leaf (26)) (.branch 17 (.leaf (47)) (.leaf (4))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (19)) (.leaf (38))) (.branch 21 (.leaf (46)) (.leaf (12)))) (.branch 24 (.branch 23 (.leaf (16)) (.leaf (27))) (.branch 25 (.leaf (48)) (.branch 26 (.leaf (58)) (.leaf (20)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (24)) (.leaf (39))) (.branch 30 (.leaf (52)) (.leaf (13)))) (.branch 33 (.branch 32 (.leaf (59)) (.leaf (28))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (49)) (.leaf (62)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (31))) (.branch 39 (.leaf (40)) (.leaf (53)))) (.branch 42 (.branch 41 (.leaf (43)) (.leaf (14))) (.branch 43 (.leaf (60)) (.branch 44 (.leaf (56)) (.leaf (29)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (64)) (.leaf (50))) (.branch 48 (.leaf (63)) (.leaf (68)))) (.branch 51 (.branch 50 (.leaf (22)) (.leaf (32))) (.branch 52 (.leaf (33)) (.branch 53 (.leaf (41)) (.leaf (45))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (54)) (.leaf (44))) (.branch 57 (.leaf (70)) (.leaf (15)))) (.branch 60 (.branch 59 (.leaf (61)) (.leaf (57))) (.branch 61 (.leaf (66)) (.branch 62 (.leaf (30)) (.leaf (65)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (51)) (.leaf (69))) (.branch 66 (.leaf (23)) (.leaf (34)))) (.branch 69 (.branch 68 (.leaf (42)) (.leaf (55))) (.branch 70 (.leaf (71)) (.branch 71 (.leaf (67)) (.leaf (35)))))))))
noncomputable def facesIndex (p : Fin 72) : Fin 72 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (10)))) (.branch 6 (.branch 5 (.leaf (17)) (.leaf (1))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (7)) (.leaf (13)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (4)) (.leaf (8))) (.branch 12 (.leaf (14)) (.leaf (21)))) (.branch 15 (.branch 14 (.leaf (30)) (.leaf (41))) (.branch 16 (.leaf (57)) (.branch 17 (.leaf (22)) (.leaf (6))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (11)) (.leaf (18))) (.branch 21 (.leaf (26)) (.leaf (36)))) (.branch 24 (.branch 23 (.leaf (49)) (.leaf (65))) (.branch 25 (.leaf (27)) (.branch 26 (.leaf (9)) (.leaf (15)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (23)) (.leaf (32))) (.branch 30 (.leaf (44)) (.leaf (61)))) (.branch 33 (.branch 32 (.leaf (37)) (.leaf (50))) (.branch 34 (.leaf (51)) (.branch 35 (.leaf (66)) (.leaf (71)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (33)) (.leaf (12))) (.branch 39 (.leaf (19)) (.leaf (28)))) (.branch 42 (.branch 41 (.leaf (38)) (.leaf (52))) (.branch 43 (.leaf (67)) (.branch 44 (.leaf (40)) (.leaf (55)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (53)) (.leaf (20))) (.branch 48 (.leaf (16)) (.leaf (24)))) (.branch 51 (.branch 50 (.leaf (34)) (.leaf (46))) (.branch 52 (.leaf (63)) (.branch 53 (.leaf (29)) (.leaf (39))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (54)) (.leaf (68))) (.branch 57 (.leaf (43)) (.leaf (59)))) (.branch 60 (.branch 59 (.leaf (25)) (.leaf (31))) (.branch 61 (.leaf (42)) (.branch 62 (.leaf (58)) (.leaf (35)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (47)) (.leaf (45))) (.branch 66 (.leaf (62)) (.leaf (60)))) (.branch 69 (.branch 68 (.leaf (70)) (.leaf (48))) (.branch 70 (.leaf (64)) (.branch 71 (.leaf (56)) (.leaf (69)))))))))
noncomputable def facesBack (p : Fin 72) : Fin 72 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 72, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 72 := by decide +kernel
theorem faces_partition : ∀ p : Fin 72, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [5,4,8,8,12,10,12,5,4,4] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 2 : Int) = 24 - 36 + 10 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.leaf (⟨-1,-3,0,-1⟩))) (.branch 12 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,0,2,1⟩)))) (.branch 15 (.branch 14 (.leaf (⟨0,1,-1,1⟩)) (.leaf (⟨1,1,1,2⟩))) (.branch 16 (.leaf (⟨2,1,1,1⟩)) (.branch 17 (.leaf (⟨-3,1,-1,0⟩)) (.leaf (⟨1,4,0,1⟩))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (⟨4,3,1,1⟩)) (.leaf (⟨1,1,-2,-1⟩))) (.branch 21 (.leaf (⟨1,-1,2,-1⟩)) (.leaf (⟨-1,-2,-1,-3⟩)))) (.branch 24 (.branch 23 (.leaf (⟨1,-2,1,-1⟩)) (.leaf (⟨-2,-3,-1,-2⟩))) (.branch 25 (.leaf (⟨-3,-2,-1,-1⟩)) (.branch 26 (.leaf (⟨3,-4,1,-1⟩)) (.leaf (⟨-4,-7,-1,-2⟩)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-2,2,3⟩))) (.branch 30 (.leaf (⟨-2,1,-3,1⟩)) (.leaf (⟨1,3,1,4⟩)))) (.branch 33 (.branch 32 (.leaf (⟨-3,2,-2,1⟩)) (.leaf (⟨2,5,1,3⟩))) (.branch 34 (.leaf (⟨-2,3,-1,1⟩)) (.branch 35 (.leaf (⟨3,5,1,2⟩)) (.leaf (⟨-7,4,-2,1⟩)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (⟨4,11,1,3⟩)) (.leaf (⟨-2,1,3,-2⟩))) (.branch 39 (.leaf (⟨1,3,-2,-5⟩)) (.leaf (⟨-2,-1,-3,-2⟩)))) (.branch 42 (.branch 41 (.leaf (⟨-5,-1,-4,-1⟩)) (.leaf (⟨1,-4,1,-3⟩))) (.branch 43 (.leaf (⟨-3,-1,-2,-1⟩)) (.branch 44 (.leaf (⟨5,-2,3,-1⟩)) (.leaf (⟨-2,-7,-1,-4⟩)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (⟨5,-3,2,-1⟩)) (.leaf (⟨-3,-8,-1,-3⟩))) (.branch 48 (.leaf (⟨-7,-3,-2,-1⟩)) (.leaf (⟨11,-4,3,-1⟩)))) (.branch 51 (.branch 50 (.leaf (⟨-4,-15,-1,-4⟩)) (.leaf (⟨-2,-1,3,1⟩))) (.branch 52 (.leaf (⟨2,3,-3,-4⟩)) (.branch 53 (.leaf (⟨3,1,-4,-1⟩)) (.leaf (⟨-1,2,-2,3⟩))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (⟨2,3,3,5⟩)) (.leaf (⟨3,2,4,3⟩))) (.branch 57 (.leaf (⟨4,1,3,1⟩)) (.leaf (⟨-1,3,-1,2⟩)))) (.branch 60 (.branch 59 (.leaf (⟨3,4,2,3⟩)) (.leaf (⟨5,3,3,2⟩))) (.branch 61 (.leaf (⟨-5,-7,-2,-3⟩)) (.branch 62 (.leaf (⟨-7,-2,-3,-1⟩)) (.leaf (⟨5,2,2,1⟩)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (⟨3,1,5,2⟩)) (.leaf (⟨11,7,3,2⟩))) (.branch 66 (.leaf (⟨-1,2,1,-3⟩)) (.leaf (⟨3,2,-5,-3⟩)))) (.branch 69 (.branch 68 (.leaf (⟨-15,-11,-4,-3⟩)) (.leaf (⟨-8,-5,-3,-2⟩))) (.branch 70 (.leaf (⟨-4,-5,-3,-4⟩)) (.branch 71 (.leaf (⟨-7,-5,-4,-3⟩)) (.leaf (⟨2,-5,1,-2⟩)))))))))
noncomputable def liftMatrix (p : Fin 72) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 72) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],13⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],14⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],15⟩,⟨⟨-3,1,-1,0⟩,[.t (3),.s,.t (0)],16⟩,⟨⟨1,4,0,1⟩,[.t (4)],17⟩,⟨⟨4,3,1,1⟩,[.t (4),.s,.t (1)],18⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],19⟩,⟨⟨1,-1,2,-1⟩,[.t (0),.s,.t (-2),.s,.t (-1)],20⟩,⟨⟨-1,-2,-1,-3⟩,[.t (1),.s,.t (3)],21⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],22⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],23⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],24⟩,⟨⟨3,-4,1,-1⟩,[.t (3),.s,.t (-1)],25⟩,⟨⟨-4,-7,-1,-2⟩,[.t (4),.s,.t (2)],26⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],27⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],28⟩,⟨⟨-2,1,-3,1⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-1)],29⟩,⟨⟨1,3,1,4⟩,[.t (1),.s,.t (4)],30⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],31⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],32⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],33⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],34⟩,⟨⟨-7,4,-2,1⟩,[.t (3),.s,.t (-2),.s,.t (-1)],35⟩,⟨⟨4,11,1,3⟩,[.t (4),.s,.t (3)],36⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],37⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],38⟩,⟨⟨-2,-1,-3,-2⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (0)],39⟩,⟨⟨-5,-1,-4,-1⟩,[.t (1),.s,.t (-4),.s,.t (0)],40⟩,⟨⟨1,-4,1,-3⟩,[.t (1),.s,.t (-3)],41⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],42⟩,⟨⟨5,-2,3,-1⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],43⟩,⟨⟨-2,-7,-1,-4⟩,[.t (2),.s,.t (4)],44⟩,⟨⟨5,-3,2,-1⟩,[.t (2),.s,.t (-2),.s,.t (-1)],45⟩,⟨⟨-3,-8,-1,-3⟩,[.t (3),.s,.t (3)],46⟩,⟨⟨-7,-3,-2,-1⟩,[.t (3),.s,.t (-2),.s,.t (0)],47⟩,⟨⟨11,-4,3,-1⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-1)],48⟩,⟨⟨-4,-15,-1,-4⟩,[.t (4),.s,.t (4)],49⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],50⟩,⟨⟨2,3,-3,-4⟩,[.t (-1),.s,.t (-3),.s,.t (1)],51⟩,⟨⟨3,1,-4,-1⟩,[.t (-1),.s,.t (-4),.s,.t (0)],52⟩,⟨⟨-1,2,-2,3⟩,[.t (0),.s,.t (-2),.s,.t (-2)],53⟩,⟨⟨2,3,3,5⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (1)],54⟩,⟨⟨3,2,4,3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],55⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],56⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],57⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],58⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],59⟩,⟨⟨-5,-7,-2,-3⟩,[.t (2),.s,.t (-2),.s,.t (1)],60⟩,⟨⟨-7,-2,-3,-1⟩,[.t (2),.s,.t (-3),.s,.t (0)],61⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],62⟩,⟨⟨3,1,5,2⟩,[.t (0),.s,.t (-2),.s,.t (-3),.s,.t (0)],63⟩,⟨⟨11,7,3,2⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (0)],64⟩,⟨⟨-1,2,1,-3⟩,[.t (-1),.s,.t (-3)],65⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],66⟩,⟨⟨-15,-11,-4,-3⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],67⟩,⟨⟨-8,-5,-3,-2⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (0)],68⟩,⟨⟨-4,-5,-3,-4⟩,[.t (1),.s,.t (-3),.s,.t (1)],69⟩,⟨⟨-7,-5,-4,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],70⟩,⟨⟨2,-5,1,-2⟩,[.t (2),.s,.t (-2)],71⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 72 ∧ ((List.finRange 72).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 72) := [⟨11,2,⟨⟨1,5,0,1⟩,[.t (5)],0⟩⟩,⟨52,8,⟨⟨-31,-27,-8,-7⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨51,4,⟨⟨15,11,-26,-19⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨66,11,⟨⟨-41,-25,-18,-11⟩,[.t (2),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨38,4,⟨⟨-19,-11,26,15⟩,[.t (-1),.s,.t (-4),.s,.t (-4),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨7,1,⟨⟨-1,0,-4,-1⟩,[.t (0),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨12,1,⟨⟨-1,0,4,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨63,9,⟨⟨-19,11,-26,15⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨54,6,⟨⟨49,-30,18,-11⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨55,9,⟨⟨15,-11,26,-19⟩,[.t (0),.s,.t (-2),.s,.t (-4),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨30,3,⟨⟨-9,8,-8,7⟩,[.t (1),.s,.t (-8),.s,.t (-1)],0⟩⟩,⟨40,3,⟨⟨7,-8,8,-9⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨69,12,⟨⟨-89,115,-24,31⟩,[.t (3),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨58,10,⟨⟨43,-61,12,-17⟩,[.t (3),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨59,7,⟨⟨27,-44,8,-13⟩,[.t (3),.s,.t (-3),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨70,13,⟨⟨-47,81,-18,31⟩,[.t (2),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-2)],0⟩⟩,⟨44,5,⟨⟨33,-59,14,-25⟩,[.t (2),.s,.t (-3),.s,.t (-5),.s,.t (-2)],0⟩⟩,⟨61,11,⟨⟨-11,25,18,-41⟩,[.t (-1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨60,5,⟨⟨-25,59,-14,33⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨68,13,⟨⟨31,-81,18,-47⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨46,6,⟨⟨-11,30,-18,49⟩,[.t (0),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨47,7,⟨⟨-13,44,-8,27⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-4)],0⟩⟩,⟨64,10,⟨⟨-17,61,-12,43⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-4)],0⟩⟩,⟨67,12,⟨⟨31,-115,24,-89⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-4)],0⟩⟩,⟨49,8,⟨⟨-7,27,8,-31⟩,[.t (-1),.s,.t (-8),.s,.t (-4)],0⟩⟩,⟨17,2,⟨⟨1,-5,0,1⟩,[.t (-5)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-3,4),(-2,3),(-3,5),(-1,2),(0,1),(1,2),(3,5),(2,3),(3,4),(1,1),(5,4),(4,3),(3,2),(5,3),(7,4),(2,1),(7,3),(5,2),(8,3),(3,1),(7,2),(11,3),(15,4),(4,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G240_89_c0

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
