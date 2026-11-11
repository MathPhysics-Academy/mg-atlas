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
namespace G96_188_c0
noncomputable def originalSData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (14)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (11))) (.branch 12 (.leaf (10)) (.leaf (7)))) (.branch 15 (.branch 14 (.leaf (19)) (.leaf (8))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (23)) (.leaf (25))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (27)) (.leaf (13))) (.branch 21 (.leaf (30)) (.leaf (15)))) (.branch 24 (.branch 23 (.leaf (31)) (.leaf (16))) (.branch 25 (.leaf (33)) (.branch 26 (.leaf (17)) (.leaf (35)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (18)) (.leaf (37))) (.branch 30 (.leaf (39)) (.leaf (20)))) (.branch 33 (.branch 32 (.leaf (22)) (.leaf (43))) (.branch 34 (.leaf (24)) (.branch 35 (.leaf (46)) (.leaf (26)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (49)) (.leaf (28))) (.branch 39 (.leaf (52)) (.leaf (29)))) (.branch 42 (.branch 41 (.leaf (53)) (.leaf (54))) (.branch 43 (.leaf (56)) (.branch 44 (.leaf (32)) (.leaf (59)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (60)) (.leaf (34))) (.branch 48 (.leaf (48)) (.leaf (47)))) (.branch 51 (.branch 50 (.leaf (36)) (.leaf (64))) (.branch 52 (.leaf (65)) (.branch 53 (.leaf (38)) (.leaf (40))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (41)) (.leaf (63))) (.branch 57 (.leaf (42)) (.leaf (67)))) (.branch 60 (.branch 59 (.leaf (66)) (.leaf (44))) (.branch 61 (.leaf (45)) (.branch 62 (.leaf (68)) (.leaf (70)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (55)) (.leaf (50))) (.branch 66 (.leaf (51)) (.leaf (58)))) (.branch 69 (.branch 68 (.leaf (57)) (.leaf (61))) (.branch 70 (.leaf (71)) (.branch 71 (.leaf (62)) (.leaf (69)))))))))
noncomputable def originalS (p : Fin 72) : Fin 72 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (10))) (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (15)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (16)) (.leaf (0))) (.branch 12 (.leaf (17)) (.leaf (18)))) (.branch 15 (.branch 14 (.leaf (20)) (.leaf (1))) (.branch 16 (.leaf (22)) (.branch 17 (.leaf (24)) (.leaf (26))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (28)) (.leaf (29))) (.branch 21 (.leaf (14)) (.leaf (30)))) (.branch 24 (.branch 23 (.leaf (32)) (.leaf (4))) (.branch 25 (.leaf (34)) (.branch 26 (.leaf (9)) (.leaf (36)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (38))) (.branch 30 (.leaf (40)) (.leaf (41)))) (.branch 33 (.branch 32 (.leaf (42)) (.leaf (44))) (.branch 34 (.leaf (45)) (.branch 35 (.leaf (47)) (.leaf (48)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (50)) (.leaf (51))) (.branch 39 (.leaf (33)) (.leaf (12)))) (.branch 42 (.branch 41 (.leaf (54)) (.leaf (55))) (.branch 43 (.leaf (57)) (.branch 44 (.leaf (58)) (.leaf (60)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (61)) (.leaf (52))) (.branch 48 (.leaf (25)) (.leaf (62)))) (.branch 51 (.branch 50 (.leaf (63)) (.leaf (65))) (.branch 52 (.leaf (66)) (.branch 53 (.leaf (67)) (.leaf (68))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (19)) (.leaf (35))) (.branch 57 (.leaf (21)) (.leaf (37)))) (.branch 60 (.branch 59 (.leaf (64)) (.leaf (69))) (.branch 61 (.leaf (23)) (.branch 62 (.leaf (39)) (.leaf (56)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (53)) (.leaf (71))) (.branch 66 (.leaf (27)) (.leaf (31)))) (.branch 69 (.branch 68 (.leaf (70)) (.leaf (59))) (.branch 70 (.leaf (49)) (.branch 71 (.leaf (46)) (.leaf (43)))))))))
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
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (14)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (11))) (.branch 12 (.leaf (10)) (.leaf (7)))) (.branch 15 (.branch 14 (.leaf (19)) (.leaf (8))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (23)) (.leaf (25))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (27)) (.leaf (13))) (.branch 21 (.leaf (30)) (.leaf (15)))) (.branch 24 (.branch 23 (.leaf (31)) (.leaf (16))) (.branch 25 (.leaf (33)) (.branch 26 (.leaf (17)) (.leaf (35)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (18)) (.leaf (37))) (.branch 30 (.leaf (39)) (.leaf (20)))) (.branch 33 (.branch 32 (.leaf (22)) (.leaf (43))) (.branch 34 (.leaf (24)) (.branch 35 (.leaf (46)) (.leaf (26)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (49)) (.leaf (28))) (.branch 39 (.leaf (52)) (.leaf (29)))) (.branch 42 (.branch 41 (.leaf (53)) (.leaf (54))) (.branch 43 (.leaf (56)) (.branch 44 (.leaf (32)) (.leaf (59)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (60)) (.leaf (34))) (.branch 48 (.leaf (48)) (.leaf (47)))) (.branch 51 (.branch 50 (.leaf (36)) (.leaf (64))) (.branch 52 (.leaf (65)) (.branch 53 (.leaf (38)) (.leaf (40))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (41)) (.leaf (63))) (.branch 57 (.leaf (42)) (.leaf (67)))) (.branch 60 (.branch 59 (.leaf (66)) (.leaf (44))) (.branch 61 (.leaf (45)) (.branch 62 (.leaf (68)) (.leaf (70)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (55)) (.leaf (50))) (.branch 66 (.leaf (51)) (.leaf (58)))) (.branch 69 (.branch 68 (.leaf (57)) (.leaf (61))) (.branch 70 (.leaf (71)) (.branch 71 (.leaf (62)) (.leaf (69)))))))))
noncomputable def S (p : Fin 72) : Fin 72 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (10))) (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (15)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (16)) (.leaf (0))) (.branch 12 (.leaf (17)) (.leaf (18)))) (.branch 15 (.branch 14 (.leaf (20)) (.leaf (1))) (.branch 16 (.leaf (22)) (.branch 17 (.leaf (24)) (.leaf (26))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (28)) (.leaf (29))) (.branch 21 (.leaf (14)) (.leaf (30)))) (.branch 24 (.branch 23 (.leaf (32)) (.leaf (4))) (.branch 25 (.leaf (34)) (.branch 26 (.leaf (9)) (.leaf (36)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (6)) (.leaf (38))) (.branch 30 (.leaf (40)) (.leaf (41)))) (.branch 33 (.branch 32 (.leaf (42)) (.leaf (44))) (.branch 34 (.leaf (45)) (.branch 35 (.leaf (47)) (.leaf (48)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (50)) (.leaf (51))) (.branch 39 (.leaf (33)) (.leaf (12)))) (.branch 42 (.branch 41 (.leaf (54)) (.leaf (55))) (.branch 43 (.leaf (57)) (.branch 44 (.leaf (58)) (.leaf (60)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (61)) (.leaf (52))) (.branch 48 (.leaf (25)) (.leaf (62)))) (.branch 51 (.branch 50 (.leaf (63)) (.leaf (65))) (.branch 52 (.leaf (66)) (.branch 53 (.leaf (67)) (.leaf (68))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (19)) (.leaf (35))) (.branch 57 (.leaf (21)) (.leaf (37)))) (.branch 60 (.branch 59 (.leaf (64)) (.leaf (69))) (.branch 61 (.leaf (23)) (.branch 62 (.leaf (39)) (.leaf (56)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (53)) (.leaf (71))) (.branch 66 (.leaf (27)) (.leaf (31)))) (.branch 69 (.branch 68 (.leaf (70)) (.leaf (59))) (.branch 70 (.leaf (49)) (.branch 71 (.leaf (46)) (.leaf (43)))))))))
noncomputable def T (p : Fin 72) : Fin 72 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (10)) (.leaf (14))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (23)) (.leaf (2))) (.branch 7 (.leaf (27)) (.branch 8 (.leaf (3)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (25)) (.leaf (5))) (.branch 12 (.leaf (6)) (.leaf (39)))) (.branch 15 (.branch 14 (.leaf (7)) (.leaf (20))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (11))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (12)) (.leaf (54))) (.branch 21 (.leaf (13)) (.leaf (56)))) (.branch 24 (.branch 23 (.leaf (15)) (.leaf (60))) (.branch 25 (.leaf (16)) (.branch 26 (.leaf (47)) (.leaf (17)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (65)) (.leaf (18))) (.branch 30 (.leaf (19)) (.leaf (21)))) (.branch 33 (.branch 32 (.leaf (66)) (.leaf (22))) (.branch 34 (.leaf (38)) (.branch 35 (.leaf (24)) (.leaf (55)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (26)) (.leaf (57))) (.branch 39 (.leaf (28)) (.leaf (61)))) (.branch 42 (.branch 41 (.leaf (29)) (.leaf (30))) (.branch 43 (.leaf (31)) (.branch 44 (.leaf (71)) (.leaf (32)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (33)) (.leaf (70))) (.branch 48 (.leaf (34)) (.leaf (35)))) (.branch 51 (.branch 50 (.leaf (69)) (.leaf (36))) (.branch 52 (.leaf (37)) (.branch 53 (.leaf (46)) (.leaf (63))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (40)) (.leaf (41))) (.branch 57 (.leaf (62)) (.leaf (42)))) (.branch 60 (.branch 59 (.leaf (43)) (.leaf (68))) (.branch 61 (.leaf (44)) (.branch 62 (.leaf (45)) (.leaf (48)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (49)) (.leaf (58))) (.branch 66 (.leaf (50)) (.leaf (51)))) (.branch 69 (.branch 68 (.leaf (52)) (.leaf (53))) (.branch 70 (.leaf (59)) (.branch 71 (.leaf (67)) (.leaf (64)))))))))
noncomputable def Ti (p : Fin 72) : Fin 72 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 72) : Fin 72 := T (S p)
theorem quotient_relations : (∀ p : Fin 72, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 72, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 72, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 72, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 72)) := [[0,3,11],[1,2,8],[4,5,16],[6,7,18],[9,10,17],[12,13,29],[14,15,30],[19,20,41],[21,22,42],[23,24,45],[25,26,48],[27,28,51],[31,32,58],[33,34,52],[35,36,63],[37,38,67],[39,40,68],[43,44,69],[46,47,62],[49,50,71],[53,54,55],[56,57,70],[59,60,61],[64,65,66]]
noncomputable def verticesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (12)) (.leaf (13))) (.branch 12 (.leaf (2)) (.leaf (15)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (18))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (8)) (.leaf (14))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (11)) (.leaf (21))) (.branch 21 (.leaf (22)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (25)) (.leaf (27))) (.branch 25 (.leaf (28)) (.branch 26 (.leaf (30)) (.leaf (31)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (33)) (.leaf (34))) (.branch 30 (.leaf (17)) (.leaf (20)))) (.branch 33 (.branch 32 (.leaf (36)) (.leaf (37))) (.branch 34 (.leaf (39)) (.branch 35 (.leaf (40)) (.leaf (42)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (43)) (.leaf (45))) (.branch 39 (.leaf (46)) (.leaf (48)))) (.branch 42 (.branch 41 (.leaf (49)) (.leaf (23))) (.branch 43 (.leaf (26)) (.branch 44 (.leaf (51)) (.leaf (52)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (29)) (.leaf (54))) (.branch 48 (.leaf (55)) (.leaf (32)))) (.branch 51 (.branch 50 (.leaf (57)) (.leaf (58))) (.branch 52 (.leaf (35)) (.branch 53 (.leaf (41)) (.leaf (60))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (61)) (.leaf (62))) (.branch 57 (.leaf (63)) (.leaf (64)))) (.branch 60 (.branch 59 (.leaf (38)) (.leaf (66))) (.branch 61 (.leaf (67)) (.branch 62 (.leaf (68)) (.leaf (56)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (44)) (.leaf (69))) (.branch 66 (.leaf (70)) (.leaf (71)))) (.branch 69 (.branch 68 (.leaf (47)) (.leaf (50))) (.branch 70 (.leaf (53)) (.branch 71 (.leaf (65)) (.leaf (59)))))))))
noncomputable def verticesIndex (p : Fin 72) : Fin 72 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (11)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (16)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (18)) (.leaf (9)))) (.branch 15 (.branch 14 (.leaf (10)) (.leaf (17))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (29))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (14)) (.leaf (15))) (.branch 21 (.leaf (30)) (.leaf (19)))) (.branch 24 (.branch 23 (.leaf (20)) (.leaf (41))) (.branch 25 (.leaf (21)) (.branch 26 (.leaf (22)) (.leaf (42)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (23)) (.leaf (24))) (.branch 30 (.leaf (45)) (.leaf (25)))) (.branch 33 (.branch 32 (.leaf (26)) (.leaf (48))) (.branch 34 (.leaf (27)) (.branch 35 (.leaf (28)) (.leaf (51)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (31)) (.leaf (32))) (.branch 39 (.leaf (58)) (.leaf (33)))) (.branch 42 (.branch 41 (.leaf (34)) (.leaf (52))) (.branch 43 (.leaf (35)) (.branch 44 (.leaf (36)) (.leaf (63)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (37)) (.leaf (38))) (.branch 48 (.leaf (67)) (.leaf (39)))) (.branch 51 (.branch 50 (.leaf (40)) (.leaf (68))) (.branch 52 (.leaf (43)) (.branch 53 (.leaf (44)) (.leaf (69))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (46)) (.leaf (47))) (.branch 57 (.leaf (62)) (.leaf (49)))) (.branch 60 (.branch 59 (.leaf (50)) (.leaf (71))) (.branch 61 (.leaf (53)) (.branch 62 (.leaf (54)) (.leaf (55)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (56)) (.leaf (57))) (.branch 66 (.leaf (70)) (.leaf (59)))) (.branch 69 (.branch 68 (.leaf (60)) (.leaf (61))) (.branch 70 (.leaf (64)) (.branch 71 (.leaf (65)) (.leaf (66)))))))))
noncomputable def verticesBack (p : Fin 72) : Fin 72 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 72, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 72 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 72, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 72)) := [[0,1],[2,4],[3,6],[5,9],[7,12],[8,14],[10,11],[13,19],[15,21],[16,23],[17,25],[18,27],[20,30],[22,31],[24,33],[26,35],[28,37],[29,39],[32,43],[34,46],[36,49],[38,52],[40,53],[41,54],[42,56],[44,59],[45,60],[47,48],[50,64],[51,65],[55,63],[57,67],[58,66],[61,68],[62,70],[69,71]]
noncomputable def edgesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (10)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (7)) (.leaf (12))) (.branch 12 (.leaf (13)) (.leaf (9)))) (.branch 15 (.branch 14 (.leaf (14)) (.leaf (11))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (18)) (.leaf (20))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (22)) (.leaf (15))) (.branch 21 (.leaf (24)) (.leaf (17)))) (.branch 24 (.branch 23 (.leaf (26)) (.leaf (19))) (.branch 25 (.leaf (28)) (.branch 26 (.leaf (21)) (.leaf (30)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (23)) (.leaf (32))) (.branch 30 (.leaf (34)) (.leaf (25)))) (.branch 33 (.branch 32 (.leaf (27)) (.leaf (36))) (.branch 34 (.leaf (29)) (.branch 35 (.leaf (38)) (.leaf (31)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (40)) (.leaf (33))) (.branch 39 (.leaf (42)) (.leaf (35)))) (.branch 42 (.branch 41 (.leaf (44)) (.leaf (46))) (.branch 43 (.leaf (48)) (.branch 44 (.leaf (37)) (.leaf (50)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (52)) (.leaf (39))) (.branch 48 (.leaf (54)) (.leaf (55)))) (.branch 51 (.branch 50 (.leaf (41)) (.leaf (56))) (.branch 52 (.leaf (58)) (.branch 53 (.leaf (43)) (.leaf (45))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (47)) (.leaf (60))) (.branch 57 (.leaf (49)) (.leaf (62)))) (.branch 60 (.branch 59 (.leaf (64)) (.leaf (51))) (.branch 61 (.leaf (53)) (.branch 62 (.leaf (66)) (.leaf (68)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (61)) (.leaf (57))) (.branch 66 (.leaf (59)) (.leaf (65)))) (.branch 69 (.branch 68 (.leaf (63)) (.leaf (67))) (.branch 70 (.leaf (70)) (.branch 71 (.leaf (69)) (.leaf (71)))))))))
noncomputable def edgesIndex (p : Fin 72) : Fin 72 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (12)) (.leaf (8))) (.branch 12 (.leaf (14)) (.leaf (10)))) (.branch 15 (.branch 14 (.leaf (11)) (.leaf (13))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (15)) (.leaf (21))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (16)) (.leaf (23))) (.branch 21 (.leaf (17)) (.leaf (25)))) (.branch 24 (.branch 23 (.leaf (18)) (.leaf (27))) (.branch 25 (.leaf (20)) (.branch 26 (.leaf (30)) (.leaf (22)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (31)) (.leaf (24))) (.branch 30 (.leaf (33)) (.leaf (26)))) (.branch 33 (.branch 32 (.leaf (35)) (.leaf (28))) (.branch 34 (.leaf (37)) (.branch 35 (.leaf (29)) (.leaf (39)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (32)) (.leaf (43))) (.branch 39 (.leaf (34)) (.leaf (46)))) (.branch 42 (.branch 41 (.leaf (36)) (.leaf (49))) (.branch 43 (.leaf (38)) (.branch 44 (.leaf (52)) (.leaf (40)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (53)) (.leaf (41))) (.branch 48 (.leaf (54)) (.leaf (42)))) (.branch 51 (.branch 50 (.leaf (56)) (.leaf (44))) (.branch 52 (.leaf (59)) (.branch 53 (.leaf (45)) (.leaf (60))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (47)) (.leaf (48))) (.branch 57 (.leaf (50)) (.leaf (64)))) (.branch 60 (.branch 59 (.leaf (51)) (.leaf (65))) (.branch 61 (.leaf (55)) (.branch 62 (.leaf (63)) (.leaf (57)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (67)) (.leaf (58))) (.branch 66 (.leaf (66)) (.leaf (61)))) (.branch 69 (.branch 68 (.leaf (68)) (.leaf (62))) (.branch 70 (.leaf (70)) (.branch 71 (.leaf (69)) (.leaf (71)))))))))
noncomputable def edgesBack (p : Fin 72) : Fin 72 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 72, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 72 := by decide +kernel
theorem edges_partition : ∀ p : Fin 72, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 72)) := [[0,2,5,10],[1,3,7,13,20,14],[4,8,15,22,32,44,60,23],[6,11,17,26,36,50,65,27],[9,16,24,34,47,25],[12,18,28,38,33,45,61,39],[19,29,40,54],[21,30,41,55,35,48,62,56],[31,42,57,37,51,66],[43,58,64,71],[46,52,67,70],[49,63,53,68,59,69]]
noncomputable def facesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (4))) (.branch 3 (.leaf (1)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (10)) (.leaf (2))) (.branch 7 (.leaf (18)) (.branch 8 (.leaf (6)) (.leaf (11)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (26)) (.leaf (3))) (.branch 12 (.leaf (19)) (.leaf (32)))) (.branch 15 (.branch 14 (.leaf (7)) (.leaf (9))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (27)) (.leaf (20))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (33)) (.leaf (40))) (.branch 21 (.leaf (8)) (.leaf (44)))) (.branch 24 (.branch 23 (.leaf (13)) (.leaf (17))) (.branch 25 (.leaf (28)) (.branch 26 (.leaf (31)) (.leaf (21)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (25)) (.leaf (34))) (.branch 30 (.leaf (41)) (.leaf (45)))) (.branch 33 (.branch 32 (.leaf (52)) (.leaf (14))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (29)) (.leaf (48)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (22)) (.leaf (55))) (.branch 39 (.leaf (35)) (.leaf (39)))) (.branch 42 (.branch 41 (.leaf (42)) (.leaf (46))) (.branch 43 (.leaf (53)) (.branch 44 (.leaf (58)) (.leaf (15)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (37)) (.leaf (62))) (.branch 48 (.leaf (30)) (.leaf (49)))) (.branch 51 (.branch 50 (.leaf (66)) (.leaf (23))) (.branch 52 (.leaf (56)) (.branch 53 (.leaf (63)) (.leaf (68))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (43)) (.leaf (47))) (.branch 57 (.leaf (51)) (.leaf (54)))) (.branch 60 (.branch 59 (.leaf (59)) (.leaf (70))) (.branch 61 (.leaf (16)) (.branch 62 (.leaf (38)) (.leaf (50)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (67)) (.leaf (60))) (.branch 66 (.leaf (24)) (.leaf (57)))) (.branch 69 (.branch 68 (.leaf (64)) (.leaf (69))) (.branch 70 (.leaf (71)) (.branch 71 (.leaf (65)) (.leaf (61)))))))))
noncomputable def facesIndex (p : Fin 72) : Fin 72 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (10)))) (.branch 6 (.branch 5 (.leaf (1)) (.leaf (3))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (13)) (.leaf (20)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (14)) (.leaf (4))) (.branch 12 (.leaf (8)) (.leaf (15)))) (.branch 15 (.branch 14 (.leaf (22)) (.leaf (32))) (.branch 16 (.leaf (44)) (.branch 17 (.leaf (60)) (.leaf (23))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (6)) (.leaf (11))) (.branch 21 (.leaf (17)) (.leaf (26)))) (.branch 24 (.branch 23 (.leaf (36)) (.leaf (50))) (.branch 25 (.leaf (65)) (.branch 26 (.leaf (27)) (.leaf (9)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (16)) (.leaf (24))) (.branch 30 (.leaf (34)) (.leaf (47)))) (.branch 33 (.branch 32 (.leaf (25)) (.leaf (12))) (.branch 34 (.leaf (18)) (.branch 35 (.leaf (28)) (.leaf (38)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (33)) (.leaf (45))) (.branch 39 (.leaf (61)) (.leaf (39)))) (.branch 42 (.branch 41 (.leaf (19)) (.leaf (29))) (.branch 43 (.leaf (40)) (.branch 44 (.leaf (54)) (.leaf (21)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (30)) (.leaf (41))) (.branch 48 (.leaf (55)) (.leaf (35)))) (.branch 51 (.branch 50 (.leaf (48)) (.leaf (62))) (.branch 52 (.leaf (56)) (.branch 53 (.leaf (31)) (.leaf (42))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (57)) (.leaf (37))) (.branch 57 (.leaf (51)) (.leaf (66)))) (.branch 60 (.branch 59 (.leaf (43)) (.leaf (58))) (.branch 61 (.leaf (64)) (.branch 62 (.leaf (71)) (.leaf (46)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (52)) (.leaf (67))) (.branch 66 (.leaf (70)) (.leaf (49)))) (.branch 69 (.branch 68 (.leaf (63)) (.leaf (53))) (.branch 70 (.leaf (68)) (.branch 71 (.leaf (59)) (.leaf (69)))))))))
noncomputable def facesBack (p : Fin 72) : Fin 72 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 72, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 72 := by decide +kernel
theorem faces_partition : ∀ p : Fin 72, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [4,6,8,8,6,8,4,8,6,4,4,6] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 1 : Int) = 24 - 36 + 12 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.leaf (⟨-1,-3,0,-1⟩))) (.branch 12 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,0,-2,1⟩)))) (.branch 15 (.branch 14 (.leaf (⟨0,-1,1,3⟩)) (.leaf (⟨0,1,-1,1⟩))) (.branch 16 (.leaf (⟨1,1,1,2⟩)) (.branch 17 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨-3,-2,-1,-1⟩))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (⟨1,1,-2,-1⟩)) (.leaf (⟨-1,0,-3,-1⟩))) (.branch 21 (.leaf (⟨0,-1,1,-2⟩)) (.leaf (⟨1,-1,2,-1⟩)))) (.branch 24 (.branch 23 (.leaf (⟨-1,-2,-1,-3⟩)) (.leaf (⟨1,-2,1,-1⟩))) (.branch 25 (.leaf (⟨-2,-3,-1,-2⟩)) (.branch 26 (.leaf (⟨-2,3,-1,1⟩)) (.leaf (⟨3,5,1,2⟩)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-2,2,3⟩))) (.branch 30 (.leaf (⟨-1,-1,3,2⟩)) (.leaf (⟨1,0,2,1⟩)))) (.branch 33 (.branch 32 (.leaf (⟨-2,1,-3,1⟩)) (.leaf (⟨1,3,1,4⟩))) (.branch 34 (.leaf (⟨-3,2,-2,1⟩)) (.branch 35 (.leaf (⟨2,5,1,3⟩)) (.leaf (⟨5,-3,2,-1⟩)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (⟨-3,-8,-1,-3⟩)) (.leaf (⟨-2,1,3,-2⟩))) (.branch 39 (.leaf (⟨1,3,-2,-5⟩)) (.leaf (⟨-1,1,2,-3⟩)))) (.branch 42 (.branch 41 (.leaf (⟨1,2,-3,-5⟩)) (.leaf (⟨-1,-1,-2,-3⟩))) (.branch 43 (.leaf (⟨-2,-1,-3,-2⟩)) (.branch 44 (.leaf (⟨-5,-1,-4,-1⟩)) (.leaf (⟨1,-4,1,-3⟩)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (⟨-3,-1,-2,-1⟩)) (.leaf (⟨-7,-2,-3,-1⟩))) (.branch 48 (.leaf (⟨2,-5,1,-2⟩)) (.leaf (⟨5,2,2,1⟩)))) (.branch 51 (.branch 50 (.leaf (⟨-8,3,-3,1⟩)) (.leaf (⟨3,11,1,4⟩))) (.branch 52 (.leaf (⟨-2,-1,3,1⟩)) (.branch 53 (.leaf (⟨5,3,3,2⟩)) (.leaf (⟨2,1,5,3⟩))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (⟨-1,1,-3,2⟩)) (.leaf (⟨1,2,2,5⟩))) (.branch 57 (.leaf (⟨-1,2,-2,3⟩)) (.leaf (⟨2,3,3,5⟩)))) (.branch 60 (.branch 59 (.leaf (⟨3,2,4,3⟩)) (.leaf (⟨4,1,3,1⟩))) (.branch 61 (.leaf (⟨-1,3,-1,2⟩)) (.branch 62 (.leaf (⟨3,4,2,3⟩)) (.leaf (⟨-5,-7,-2,-3⟩)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (⟨-8,-5,-3,-2⟩)) (.leaf (⟨3,1,-4,-1⟩))) (.branch 66 (.leaf (⟨-1,2,1,-3⟩)) (.leaf (⟨2,3,-3,-4⟩)))) (.branch 69 (.branch 68 (.leaf (⟨3,2,-5,-3⟩)) (.leaf (⟨2,1,-5,-2⟩))) (.branch 70 (.leaf (⟨-4,-5,-3,-4⟩)) (.branch 71 (.leaf (⟨3,1,5,2⟩)) (.leaf (⟨11,8,4,3⟩)))))))))
noncomputable def liftMatrix (p : Fin 72) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 72) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],12⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],13⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],14⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],15⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],16⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],17⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],18⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],19⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],20⟩,⟨⟨1,-1,2,-1⟩,[.t (0),.s,.t (-2),.s,.t (-1)],21⟩,⟨⟨-1,-2,-1,-3⟩,[.t (1),.s,.t (3)],22⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],23⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],24⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],25⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],26⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],27⟩,⟨⟨-1,-2,2,3⟩,[.t (-1),.s,.t (-2),.s,.t (1)],28⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],29⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],30⟩,⟨⟨-2,1,-3,1⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-1)],31⟩,⟨⟨1,3,1,4⟩,[.t (1),.s,.t (4)],32⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],33⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],34⟩,⟨⟨5,-3,2,-1⟩,[.t (2),.s,.t (-2),.s,.t (-1)],35⟩,⟨⟨-3,-8,-1,-3⟩,[.t (3),.s,.t (3)],36⟩,⟨⟨-2,1,3,-2⟩,[.t (-1),.s,.t (-3),.s,.t (-1)],37⟩,⟨⟨1,3,-2,-5⟩,[.t (-1),.s,.t (-2),.s,.t (2)],38⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],39⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],40⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],41⟩,⟨⟨-2,-1,-3,-2⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (0)],42⟩,⟨⟨-5,-1,-4,-1⟩,[.t (1),.s,.t (-4),.s,.t (0)],43⟩,⟨⟨1,-4,1,-3⟩,[.t (1),.s,.t (-3)],44⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],45⟩,⟨⟨-7,-2,-3,-1⟩,[.t (2),.s,.t (-3),.s,.t (0)],46⟩,⟨⟨2,-5,1,-2⟩,[.t (2),.s,.t (-2)],47⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],48⟩,⟨⟨-8,3,-3,1⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],49⟩,⟨⟨3,11,1,4⟩,[.t (3),.s,.t (4)],50⟩,⟨⟨-2,-1,3,1⟩,[.t (-1),.s,.t (-3),.s,.t (0)],51⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],52⟩,⟨⟨2,1,5,3⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (0)],53⟩,⟨⟨-1,1,-3,2⟩,[.t (0),.s,.t (-3),.s,.t (-1)],54⟩,⟨⟨1,2,2,5⟩,[.t (0),.s,.t (-2),.s,.t (2)],55⟩,⟨⟨-1,2,-2,3⟩,[.t (0),.s,.t (-2),.s,.t (-2)],56⟩,⟨⟨2,3,3,5⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (1)],57⟩,⟨⟨3,2,4,3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],58⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],59⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],60⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],61⟩,⟨⟨-5,-7,-2,-3⟩,[.t (2),.s,.t (-2),.s,.t (1)],62⟩,⟨⟨-8,-5,-3,-2⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (0)],63⟩,⟨⟨3,1,-4,-1⟩,[.t (-1),.s,.t (-4),.s,.t (0)],64⟩,⟨⟨-1,2,1,-3⟩,[.t (-1),.s,.t (-3)],65⟩,⟨⟨2,3,-3,-4⟩,[.t (-1),.s,.t (-3),.s,.t (1)],66⟩,⟨⟨3,2,-5,-3⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (0)],67⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],68⟩,⟨⟨-4,-5,-3,-4⟩,[.t (1),.s,.t (-3),.s,.t (1)],69⟩,⟨⟨3,1,5,2⟩,[.t (0),.s,.t (-2),.s,.t (-3),.s,.t (0)],70⟩,⟨⟨11,8,4,3⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],71⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 72 ∧ ((List.finRange 72).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 72) := [⟨11,1,⟨⟨1,4,0,1⟩,[.t (4)],0⟩⟩,⟨64,7,⟨⟨23,20,8,7⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨66,10,⟨⟨17,12,24,17⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨67,9,⟨⟨19,12,30,19⟩,[.t (0),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨38,5,⟨⟨-25,-14,-16,-9⟩,[.t (1),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨68,11,⟨⟨23,10,16,7⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨40,6,⟨⟨-11,-4,-30,-11⟩,[.t (0),.s,.t (-3),.s,.t (-4),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨13,2,⟨⟨-1,0,-6,-1⟩,[.t (0),.s,.t (-6),.s,.t (0)],0⟩⟩,⟨19,2,⟨⟨-1,0,6,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨53,6,⟨⟨-11,4,30,-11⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨55,8,⟨⟨-41,18,-16,7⟩,[.t (2),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨70,12,⟨⟨39,-22,16,-9⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨57,9,⟨⟨19,-12,-30,19⟩,[.t (-1),.s,.t (-3),.s,.t (-4),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨58,10,⟨⟨17,-12,-24,17⟩,[.t (-1),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨32,3,⟨⟨-9,8,-8,7⟩,[.t (1),.s,.t (-8),.s,.t (-1)],0⟩⟩,⟨43,3,⟨⟨7,-8,8,-9⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨69,13,⟨⟨-65,84,-24,31⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨61,11,⟨⟨7,-10,-16,23⟩,[.t (-1),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨52,5,⟨⟨-9,14,16,-25⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨34,4,⟨⟨-13,24,-6,11⟩,[.t (2),.s,.t (-6),.s,.t (-2)],0⟩⟩,⟨46,4,⟨⟨11,-24,6,-13⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨62,12,⟨⟨-9,22,-16,39⟩,[.t (0),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨63,8,⟨⟨7,-18,16,-41⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3)],0⟩⟩,⟨71,13,⟨⟨31,-84,24,-65⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨50,7,⟨⟨7,-20,-8,23⟩,[.t (-1),.s,.t (-8),.s,.t (-3)],0⟩⟩,⟨10,1,⟨⟨1,-4,0,1⟩,[.t (-4)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-3,4),(-2,3),(-3,5),(-1,2),(-2,5),(-1,3),(0,1),(1,3),(2,5),(1,2),(3,5),(2,3),(3,4),(1,1),(5,4),(4,3),(3,2),(5,3),(2,1),(7,3),(5,2),(8,3),(11,4),(3,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G96_188_c0

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
