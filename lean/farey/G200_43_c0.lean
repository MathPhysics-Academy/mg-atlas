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
namespace G200_43_c0
noncomputable def originalSData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (8)) (.branch 8 (.leaf (10)) (.leaf (6)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (13)) (.leaf (7))) (.branch 12 (.leaf (12)) (.leaf (11)))) (.branch 15 (.branch 14 (.leaf (9)) (.leaf (17))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (21)) (.leaf (14))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (24)) (.leaf (15))) (.branch 21 (.leaf (26)) (.leaf (16)))) (.branch 24 (.branch 23 (.leaf (28)) (.leaf (29))) (.branch 25 (.leaf (18)) (.branch 26 (.leaf (32)) (.leaf (20)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (35)) (.leaf (22))) (.branch 30 (.leaf (23)) (.leaf (38)))) (.branch 33 (.branch 32 (.leaf (40)) (.leaf (25))) (.branch 34 (.leaf (34)) (.branch 35 (.leaf (33)) (.leaf (27)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (45)) (.leaf (47))) (.branch 39 (.leaf (30)) (.leaf (49)))) (.branch 42 (.branch 41 (.leaf (31)) (.leaf (51))) (.branch 43 (.leaf (52)) (.branch 44 (.leaf (54)) (.leaf (55)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (36)) (.leaf (58))) (.branch 48 (.leaf (37)) (.leaf (57)))) (.branch 51 (.branch 50 (.leaf (39)) (.leaf (56))) (.branch 52 (.leaf (41)) (.branch 53 (.leaf (42)) (.leaf (61))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (43)) (.leaf (44))) (.branch 57 (.leaf (50)) (.leaf (48)))) (.branch 60 (.branch 59 (.leaf (46)) (.leaf (63))) (.branch 61 (.leaf (65)) (.branch 62 (.leaf (53)) (.leaf (67)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (59)) (.leaf (69))) (.branch 66 (.leaf (60)) (.leaf (70)))) (.branch 69 (.branch 68 (.leaf (62)) (.leaf (71))) (.branch 70 (.leaf (64)) (.branch 71 (.leaf (66)) (.leaf (68)))))))))
noncomputable def originalS (p : Fin 72) : Fin 72 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (0)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (4))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (12)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (14)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (15)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (18))) (.branch 16 (.leaf (20)) (.branch 17 (.leaf (22)) (.leaf (23))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (25)) (.leaf (10))) (.branch 21 (.leaf (27)) (.leaf (8)))) (.branch 24 (.branch 23 (.leaf (29)) (.leaf (30))) (.branch 25 (.leaf (31)) (.branch 26 (.leaf (33)) (.leaf (34)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (36)) (.leaf (37))) (.branch 30 (.leaf (13)) (.leaf (39)))) (.branch 33 (.branch 32 (.leaf (41)) (.leaf (42))) (.branch 34 (.leaf (19)) (.branch 35 (.leaf (43)) (.leaf (44)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (46)) (.leaf (48))) (.branch 39 (.leaf (28)) (.leaf (50)))) (.branch 42 (.branch 41 (.leaf (17)) (.leaf (52))) (.branch 43 (.leaf (53)) (.branch 44 (.leaf (55)) (.leaf (56)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (57)) (.leaf (59))) (.branch 48 (.leaf (21)) (.leaf (35)))) (.branch 51 (.branch 50 (.leaf (60)) (.leaf (54))) (.branch 52 (.leaf (61)) (.branch 53 (.leaf (24)) (.leaf (40))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (32)) (.leaf (26))) (.branch 57 (.leaf (62)) (.leaf (63)))) (.branch 60 (.branch 59 (.leaf (64)) (.leaf (47))) (.branch 61 (.leaf (66)) (.branch 62 (.leaf (51)) (.leaf (68)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (69)) (.leaf (58))) (.branch 66 (.leaf (38)) (.leaf (67)))) (.branch 69 (.branch 68 (.leaf (49)) (.leaf (65))) (.branch 70 (.leaf (45)) (.branch 71 (.leaf (71)) (.leaf (70)))))))))
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
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (5)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (3))) (.branch 7 (.leaf (8)) (.branch 8 (.leaf (10)) (.leaf (6)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (13)) (.leaf (7))) (.branch 12 (.leaf (12)) (.leaf (11)))) (.branch 15 (.branch 14 (.leaf (9)) (.leaf (17))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (21)) (.leaf (14))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (24)) (.leaf (15))) (.branch 21 (.leaf (26)) (.leaf (16)))) (.branch 24 (.branch 23 (.leaf (28)) (.leaf (29))) (.branch 25 (.leaf (18)) (.branch 26 (.leaf (32)) (.leaf (20)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (35)) (.leaf (22))) (.branch 30 (.leaf (23)) (.leaf (38)))) (.branch 33 (.branch 32 (.leaf (40)) (.leaf (25))) (.branch 34 (.leaf (34)) (.branch 35 (.leaf (33)) (.leaf (27)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (45)) (.leaf (47))) (.branch 39 (.leaf (30)) (.leaf (49)))) (.branch 42 (.branch 41 (.leaf (31)) (.leaf (51))) (.branch 43 (.leaf (52)) (.branch 44 (.leaf (54)) (.leaf (55)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (36)) (.leaf (58))) (.branch 48 (.leaf (37)) (.leaf (57)))) (.branch 51 (.branch 50 (.leaf (39)) (.leaf (56))) (.branch 52 (.leaf (41)) (.branch 53 (.leaf (42)) (.leaf (61))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (43)) (.leaf (44))) (.branch 57 (.leaf (50)) (.leaf (48)))) (.branch 60 (.branch 59 (.leaf (46)) (.leaf (63))) (.branch 61 (.leaf (65)) (.branch 62 (.leaf (53)) (.leaf (67)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (59)) (.leaf (69))) (.branch 66 (.leaf (60)) (.leaf (70)))) (.branch 69 (.branch 68 (.leaf (62)) (.leaf (71))) (.branch 70 (.leaf (64)) (.branch 71 (.leaf (66)) (.leaf (68)))))))))
noncomputable def S (p : Fin 72) : Fin 72 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (0)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (7)) (.leaf (4))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (12)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (14)) (.leaf (1))) (.branch 12 (.leaf (5)) (.leaf (15)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (18))) (.branch 16 (.leaf (20)) (.branch 17 (.leaf (22)) (.leaf (23))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (25)) (.leaf (10))) (.branch 21 (.leaf (27)) (.leaf (8)))) (.branch 24 (.branch 23 (.leaf (29)) (.leaf (30))) (.branch 25 (.leaf (31)) (.branch 26 (.leaf (33)) (.leaf (34)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (36)) (.leaf (37))) (.branch 30 (.leaf (13)) (.leaf (39)))) (.branch 33 (.branch 32 (.leaf (41)) (.leaf (42))) (.branch 34 (.leaf (19)) (.branch 35 (.leaf (43)) (.leaf (44)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (46)) (.leaf (48))) (.branch 39 (.leaf (28)) (.leaf (50)))) (.branch 42 (.branch 41 (.leaf (17)) (.leaf (52))) (.branch 43 (.leaf (53)) (.branch 44 (.leaf (55)) (.leaf (56)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (57)) (.leaf (59))) (.branch 48 (.leaf (21)) (.leaf (35)))) (.branch 51 (.branch 50 (.leaf (60)) (.leaf (54))) (.branch 52 (.leaf (61)) (.branch 53 (.leaf (24)) (.leaf (40))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (32)) (.leaf (26))) (.branch 57 (.leaf (62)) (.leaf (63)))) (.branch 60 (.branch 59 (.leaf (64)) (.leaf (47))) (.branch 61 (.leaf (66)) (.branch 62 (.leaf (51)) (.leaf (68)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (69)) (.leaf (58))) (.branch 66 (.leaf (38)) (.leaf (67)))) (.branch 69 (.branch 68 (.leaf (49)) (.leaf (65))) (.branch 70 (.leaf (45)) (.branch 71 (.leaf (71)) (.leaf (70)))))))))
noncomputable def T (p : Fin 72) : Fin 72 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (10))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (11))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (4)) (.leaf (21)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (19))) (.branch 12 (.leaf (7)) (.leaf (8)))) (.branch 15 (.branch 14 (.leaf (29)) (.leaf (9))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (40))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (14)) (.leaf (33))) (.branch 21 (.leaf (15)) (.leaf (47)))) (.branch 24 (.branch 23 (.leaf (16)) (.leaf (17))) (.branch 25 (.leaf (52)) (.branch 26 (.leaf (18)) (.leaf (55)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (20)) (.leaf (38))) (.branch 30 (.leaf (22)) (.leaf (23)))) (.branch 33 (.branch 32 (.leaf (24)) (.leaf (54))) (.branch 34 (.leaf (25)) (.branch 35 (.leaf (26)) (.leaf (48)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (27)) (.leaf (28))) (.branch 39 (.leaf (65)) (.leaf (30)))) (.branch 42 (.branch 41 (.leaf (53)) (.leaf (31))) (.branch 43 (.leaf (32)) (.branch 44 (.leaf (34)) (.leaf (35)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (69)) (.leaf (36))) (.branch 48 (.leaf (59)) (.leaf (37)))) (.branch 51 (.branch 50 (.leaf (67)) (.leaf (39))) (.branch 52 (.leaf (61)) (.branch 53 (.leaf (41)) (.leaf (42))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (50)) (.leaf (43))) (.branch 57 (.leaf (44)) (.leaf (45)))) (.branch 60 (.branch 59 (.leaf (64)) (.leaf (46))) (.branch 61 (.leaf (49)) (.branch 62 (.leaf (51)) (.leaf (56)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (57)) (.leaf (58))) (.branch 66 (.leaf (68)) (.leaf (60)))) (.branch 69 (.branch 68 (.leaf (66)) (.leaf (62))) (.branch 70 (.leaf (63)) (.branch 71 (.leaf (71)) (.leaf (70)))))))))
noncomputable def Ti (p : Fin 72) : Fin 72 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 72) : Fin 72 := T (S p)
theorem quotient_relations : (∀ p : Fin 72, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 72, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 72, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 72, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 72)) := [[0,3,4],[1,2,7],[5,6,12],[8,9,16],[10,11,15],[13,14,23],[17,18,31],[19,20,34],[21,22,37],[24,25,42],[26,27,44],[28,29,30],[32,33,43],[35,36,57],[38,39,60],[40,41,61],[45,46,64],[47,48,63],[49,50,62],[51,52,53],[54,55,56],[58,59,69],[65,66,71],[67,68,70]]
noncomputable def verticesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (6))) (.branch 7 (.leaf (7)) (.branch 8 (.leaf (5)) (.leaf (9)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (10)) (.leaf (12))) (.branch 12 (.leaf (13)) (.leaf (8)))) (.branch 15 (.branch 14 (.leaf (15)) (.leaf (16))) (.branch 16 (.leaf (14)) (.branch 17 (.leaf (11)) (.leaf (18))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (19)) (.leaf (21))) (.branch 21 (.leaf (22)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (25)) (.leaf (17))) (.branch 25 (.leaf (27)) (.branch 26 (.leaf (28)) (.leaf (30)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (31)) (.leaf (33))) (.branch 30 (.leaf (34)) (.leaf (35)))) (.branch 33 (.branch 32 (.leaf (20)) (.leaf (36))) (.branch 34 (.leaf (37)) (.branch 35 (.leaf (23)) (.leaf (39)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (40)) (.leaf (26))) (.branch 39 (.leaf (42)) (.leaf (43)))) (.branch 42 (.branch 41 (.leaf (45)) (.leaf (46))) (.branch 43 (.leaf (29)) (.branch 44 (.leaf (38)) (.leaf (32)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (48)) (.leaf (49))) (.branch 48 (.leaf (51)) (.leaf (52)))) (.branch 51 (.branch 50 (.leaf (54)) (.leaf (55))) (.branch 52 (.leaf (57)) (.branch 53 (.leaf (58)) (.leaf (59))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (60)) (.leaf (61))) (.branch 57 (.leaf (62)) (.leaf (41)))) (.branch 60 (.branch 59 (.leaf (63)) (.leaf (64))) (.branch 61 (.leaf (44)) (.branch 62 (.leaf (47)) (.leaf (56)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (53)) (.leaf (50))) (.branch 66 (.leaf (66)) (.leaf (67)))) (.branch 69 (.branch 68 (.leaf (69)) (.leaf (70))) (.branch 70 (.leaf (65)) (.branch 71 (.leaf (71)) (.leaf (68)))))))))
noncomputable def verticesIndex (p : Fin 72) : Fin 72 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (7))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (6)) (.leaf (12)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (8)) (.leaf (9))) (.branch 12 (.leaf (16)) (.leaf (10)))) (.branch 15 (.branch 14 (.leaf (11)) (.leaf (15))) (.branch 16 (.leaf (13)) (.branch 17 (.leaf (14)) (.leaf (23))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (17)) (.leaf (18))) (.branch 21 (.leaf (31)) (.leaf (19)))) (.branch 24 (.branch 23 (.leaf (20)) (.leaf (34))) (.branch 25 (.leaf (21)) (.branch 26 (.leaf (22)) (.leaf (37)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (24)) (.leaf (25))) (.branch 30 (.leaf (42)) (.leaf (26)))) (.branch 33 (.branch 32 (.leaf (27)) (.leaf (44))) (.branch 34 (.leaf (28)) (.branch 35 (.leaf (29)) (.leaf (30)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (32)) (.leaf (33))) (.branch 39 (.leaf (43)) (.leaf (35)))) (.branch 42 (.branch 41 (.leaf (36)) (.leaf (57))) (.branch 43 (.leaf (38)) (.branch 44 (.leaf (39)) (.leaf (60)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (40)) (.leaf (41))) (.branch 48 (.leaf (61)) (.leaf (45)))) (.branch 51 (.branch 50 (.leaf (46)) (.leaf (64))) (.branch 52 (.leaf (47)) (.branch 53 (.leaf (48)) (.leaf (63))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (49)) (.leaf (50))) (.branch 57 (.leaf (62)) (.leaf (51)))) (.branch 60 (.branch 59 (.leaf (52)) (.leaf (53))) (.branch 61 (.leaf (54)) (.branch 62 (.leaf (55)) (.leaf (56)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (58)) (.leaf (59))) (.branch 66 (.leaf (69)) (.leaf (65)))) (.branch 69 (.branch 68 (.leaf (66)) (.leaf (71))) (.branch 70 (.leaf (67)) (.branch 71 (.leaf (68)) (.leaf (70)))))))))
noncomputable def verticesBack (p : Fin 72) : Fin 72 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 72, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 72 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 72, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 72)) := [[0,1],[2,4],[3,5],[6,8],[7,10],[9,13],[11,12],[14,17],[15,19],[16,21],[18,24],[20,26],[22,28],[23,29],[25,32],[27,35],[30,38],[31,40],[33,34],[36,45],[37,47],[39,49],[41,51],[42,52],[43,54],[44,55],[46,58],[48,57],[50,56],[53,61],[59,63],[60,65],[62,67],[64,69],[66,70],[68,71]]
noncomputable def edgesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (8)) (.leaf (7)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (10)) (.leaf (9))) (.branch 12 (.leaf (12)) (.leaf (13)))) (.branch 15 (.branch 14 (.leaf (11)) (.leaf (14))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (18)) (.leaf (15))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (20)) (.leaf (17))) (.branch 21 (.leaf (22)) (.leaf (19)))) (.branch 24 (.branch 23 (.leaf (24)) (.leaf (26))) (.branch 25 (.leaf (21)) (.branch 26 (.leaf (28)) (.leaf (23)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (30)) (.leaf (25))) (.branch 30 (.leaf (27)) (.leaf (32)))) (.branch 33 (.branch 32 (.leaf (34)) (.leaf (29))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (37)) (.leaf (31)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (38)) (.leaf (40))) (.branch 39 (.leaf (33)) (.leaf (42)))) (.branch 42 (.branch 41 (.leaf (35)) (.leaf (44))) (.branch 43 (.leaf (46)) (.branch 44 (.leaf (48)) (.leaf (50)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (39)) (.leaf (52))) (.branch 48 (.leaf (41)) (.leaf (54)))) (.branch 51 (.branch 50 (.leaf (43)) (.leaf (56))) (.branch 52 (.leaf (45)) (.branch 53 (.leaf (47)) (.leaf (58))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (49)) (.leaf (51))) (.branch 57 (.leaf (57)) (.leaf (55)))) (.branch 60 (.branch 59 (.leaf (53)) (.leaf (60))) (.branch 61 (.leaf (62)) (.branch 62 (.leaf (59)) (.leaf (64)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (61)) (.leaf (66))) (.branch 66 (.leaf (63)) (.leaf (68)))) (.branch 69 (.branch 68 (.leaf (65)) (.leaf (70))) (.branch 70 (.leaf (67)) (.branch 71 (.leaf (69)) (.leaf (71)))))))))
noncomputable def edgesIndex (p : Fin 72) : Fin 72 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (5))) (.branch 7 (.leaf (6)) (.branch 8 (.leaf (8)) (.leaf (7)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (10)) (.leaf (9))) (.branch 12 (.leaf (13)) (.leaf (11)))) (.branch 15 (.branch 14 (.leaf (12)) (.leaf (14))) (.branch 16 (.leaf (17)) (.branch 17 (.leaf (15)) (.leaf (19))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (16)) (.leaf (21))) (.branch 21 (.leaf (18)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (20)) (.leaf (26))) (.branch 25 (.leaf (22)) (.branch 26 (.leaf (28)) (.leaf (23)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (29)) (.leaf (25))) (.branch 30 (.leaf (32)) (.leaf (27)))) (.branch 33 (.branch 32 (.leaf (35)) (.leaf (30))) (.branch 34 (.leaf (38)) (.branch 35 (.leaf (31)) (.leaf (40)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (33)) (.leaf (34))) (.branch 39 (.leaf (36)) (.leaf (45)))) (.branch 42 (.branch 41 (.leaf (37)) (.leaf (47))) (.branch 43 (.leaf (39)) (.branch 44 (.leaf (49)) (.leaf (41)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (51)) (.leaf (42))) (.branch 48 (.leaf (52)) (.leaf (43)))) (.branch 51 (.branch 50 (.leaf (54)) (.leaf (44))) (.branch 52 (.leaf (55)) (.branch 53 (.leaf (46)) (.leaf (58))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (48)) (.leaf (57))) (.branch 57 (.leaf (50)) (.leaf (56)))) (.branch 60 (.branch 59 (.leaf (53)) (.leaf (61))) (.branch 61 (.leaf (59)) (.branch 62 (.leaf (63)) (.leaf (60)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (65)) (.leaf (62))) (.branch 66 (.leaf (67)) (.leaf (64)))) (.branch 69 (.branch 68 (.leaf (69)) (.leaf (66))) (.branch 70 (.leaf (70)) (.branch 71 (.leaf (68)) (.leaf (71)))))))))
noncomputable def edgesBack (p : Fin 72) : Fin 72 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 72, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 72 := by decide +kernel
theorem edges_partition : ∀ p : Fin 72, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 72)) := [[0,2],[1,3,6,9,14,18,25,33,19,10],[4,7,11,5],[8,12,15,20,27,36,46,59,47,21],[13,16,22,29],[17,23,30,39,50,54,32,42,53,40],[24,31,41,52],[26,34,43,55],[28,37,48,35,44,56,62,68,65,38],[45,57,63,69],[49,60,66,67],[51,61],[58,64],[70,71]]
noncomputable def facesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (12)) (.leaf (15))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (13)) (.leaf (16)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (11))) (.branch 12 (.leaf (14)) (.leaf (17)))) (.branch 15 (.branch 14 (.leaf (26)) (.leaf (6))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (27)) (.leaf (30))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (7)) (.leaf (10))) (.branch 21 (.leaf (19)) (.leaf (25)))) (.branch 24 (.branch 23 (.leaf (28)) (.leaf (31))) (.branch 25 (.leaf (40)) (.branch 26 (.leaf (8)) (.leaf (44)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (20)) (.leaf (48))) (.branch 30 (.leaf (29)) (.leaf (32)))) (.branch 33 (.branch 32 (.leaf (41)) (.leaf (36))) (.branch 34 (.leaf (9)) (.branch 35 (.leaf (45)) (.leaf (51)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (21)) (.leaf (49))) (.branch 39 (.leaf (57)) (.leaf (33)))) (.branch 42 (.branch 41 (.leaf (39)) (.leaf (42))) (.branch 43 (.leaf (37)) (.branch 44 (.leaf (46)) (.leaf (52)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (58)) (.leaf (22))) (.branch 48 (.leaf (24)) (.leaf (50)))) (.branch 51 (.branch 50 (.leaf (62)) (.leaf (34))) (.branch 52 (.leaf (66)) (.branch 53 (.leaf (43)) (.leaf (38))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (35)) (.leaf (47))) (.branch 57 (.leaf (53)) (.leaf (59)))) (.branch 60 (.branch 59 (.leaf (68)) (.leaf (23))) (.branch 61 (.leaf (63)) (.branch 62 (.leaf (67)) (.leaf (54)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (60)) (.leaf (69))) (.branch 66 (.leaf (56)) (.leaf (64)))) (.branch 69 (.branch 68 (.leaf (65)) (.leaf (55))) (.branch 70 (.leaf (61)) (.branch 71 (.leaf (70)) (.leaf (71)))))))))
noncomputable def facesIndex (p : Fin 72) : Fin 72 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (1)) (.leaf (3)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (9))) (.branch 7 (.leaf (14)) (.branch 8 (.leaf (18)) (.leaf (25)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (33)) (.leaf (19))) (.branch 12 (.leaf (10)) (.leaf (4)))) (.branch 15 (.branch 14 (.leaf (7)) (.leaf (11))) (.branch 16 (.leaf (5)) (.branch 17 (.leaf (8)) (.leaf (12))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (15)) (.leaf (20))) (.branch 21 (.leaf (27)) (.leaf (36)))) (.branch 24 (.branch 23 (.leaf (46)) (.leaf (59))) (.branch 25 (.leaf (47)) (.branch 26 (.leaf (21)) (.leaf (13)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (16)) (.leaf (22))) (.branch 30 (.leaf (29)) (.leaf (17)))) (.branch 33 (.branch 32 (.leaf (23)) (.leaf (30))) (.branch 34 (.leaf (39)) (.branch 35 (.leaf (50)) (.leaf (54)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (32)) (.leaf (42))) (.branch 39 (.leaf (53)) (.leaf (40)))) (.branch 42 (.branch 41 (.leaf (24)) (.leaf (31))) (.branch 43 (.leaf (41)) (.branch 44 (.leaf (52)) (.leaf (26)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (34)) (.leaf (43))) (.branch 48 (.leaf (55)) (.leaf (28)))) (.branch 51 (.branch 50 (.leaf (37)) (.leaf (48))) (.branch 52 (.leaf (35)) (.branch 53 (.leaf (44)) (.leaf (56))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (62)) (.leaf (68))) (.branch 57 (.leaf (65)) (.leaf (38)))) (.branch 60 (.branch 59 (.leaf (45)) (.leaf (57))) (.branch 61 (.leaf (63)) (.branch 62 (.leaf (69)) (.leaf (49)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (60)) (.leaf (66))) (.branch 66 (.leaf (67)) (.leaf (51)))) (.branch 69 (.branch 68 (.leaf (61)) (.leaf (58))) (.branch 70 (.leaf (64)) (.branch 71 (.leaf (70)) (.leaf (71)))))))))
noncomputable def facesBack (p : Fin 72) : Fin 72 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 72, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 72 := by decide +kernel
theorem faces_partition : ∀ p : Fin 72, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [2,10,4,10,4,10,4,4,10,4,4,2,2,2] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 24 - 36 + 14 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨-1,0,1,-1⟩))) (.branch 7 (.leaf (⟨0,1,-1,-2⟩)) (.branch 8 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨1,0,-2,1⟩)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (⟨0,-1,1,3⟩)) (.leaf (⟨0,1,-1,1⟩))) (.branch 12 (.leaf (⟨1,1,1,2⟩)) (.leaf (⟨1,1,-2,-1⟩)))) (.branch 15 (.branch 14 (.leaf (⟨-1,0,3,-1⟩)) (.leaf (⟨0,1,-1,-4⟩))) (.branch 16 (.leaf (⟨1,0,2,1⟩)) (.branch 17 (.leaf (⟨-1,-1,3,2⟩)) (.leaf (⟨1,0,-4,1⟩))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (⟨0,-1,1,5⟩)) (.leaf (⟨0,-1,1,-2⟩))) (.branch 21 (.leaf (⟨-1,-1,-2,-3⟩)) (.leaf (⟨-1,1,2,-3⟩)))) (.branch 24 (.branch 23 (.leaf (⟨1,2,-3,-5⟩)) (.leaf (⟨1,1,-4,-3⟩))) (.branch 25 (.leaf (⟨-1,0,-5,-1⟩)) (.branch 26 (.leaf (⟨0,-1,1,-4⟩)) (.leaf (⟨-1,1,-3,2⟩)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (⟨1,2,2,5⟩)) (.leaf (⟨-2,-1,7,3⟩))) (.branch 30 (.leaf (⟨1,-1,-3,4⟩)) (.leaf (⟨-1,-2,4,7⟩)))) (.branch 33 (.branch 32 (.leaf (⟨-1,-1,5,4⟩)) (.leaf (⟨1,0,4,1⟩))) (.branch 34 (.leaf (⟨0,1,-1,3⟩)) (.branch 35 (.leaf (⟨-1,0,-3,-1⟩)) (.leaf (⟨2,-1,5,-2⟩)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (⟨-1,-3,-2,-7⟩)) (.leaf (⟨2,1,-5,-2⟩))) (.branch 39 (.leaf (⟨-2,1,7,-4⟩)) (.leaf (⟨1,3,-4,-11⟩)))) (.branch 42 (.branch 41 (.leaf (⟨-1,1,4,-5⟩)) (.leaf (⟨1,2,-5,-9⟩))) (.branch 43 (.leaf (⟨-1,-1,-4,-5⟩)) (.branch 44 (.leaf (⟨1,1,3,4⟩)) (.leaf (⟨2,1,5,3⟩)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (⟨-3,1,-7,2⟩)) (.leaf (⟨1,4,2,9⟩))) (.branch 48 (.leaf (⟨1,-2,-2,5⟩)) (.leaf (⟨-2,-3,5,7⟩)))) (.branch 51 (.branch 50 (.leaf (⟨5,3,13,8⟩)) (.leaf (⟨-3,2,-8,5⟩))) (.branch 52 (.leaf (⟨2,1,9,5⟩)) (.branch 53 (.leaf (⟨-1,1,-5,4⟩)) (.leaf (⟨1,2,4,9⟩))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (⟨-3,-1,-8,-3⟩)) (.leaf (⟨1,-2,3,-5⟩))) (.branch 57 (.leaf (⟨-2,-3,-5,-8⟩)) (.leaf (⟨-3,-2,-7,-5⟩)))) (.branch 60 (.branch 59 (.leaf (⟨4,1,-9,-2⟩)) (.leaf (⟨-1,3,2,-7⟩))) (.branch 61 (.leaf (⟨3,2,-11,-7⟩)) (.branch 62 (.leaf (⟨2,1,-9,-4⟩)) (.leaf (⟨2,5,5,13⟩)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (⟨-3,-1,7,2⟩)) (.leaf (⟨4,3,9,7⟩))) (.branch 66 (.leaf (⟨2,-3,-7,11⟩)) (.leaf (⟨-3,-5,11,18⟩)))) (.branch 69 (.branch 68 (.leaf (⟨5,-2,13,-5⟩)) (.leaf (⟨-2,-7,-5,-18⟩))) (.branch 70 (.leaf (⟨3,4,-7,-9⟩)) (.branch 71 (.leaf (⟨-7,-5,-18,-13⟩)) (.leaf (⟨-5,-2,18,7⟩)))))))))
noncomputable def liftMatrix (p : Fin 72) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 72) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],4⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],5⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],6⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],7⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],8⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],9⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],10⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],11⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],12⟩,⟨⟨-1,0,3,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],13⟩,⟨⟨0,1,-1,-4⟩,[.t (0),.s,.t (4)],14⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],15⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],16⟩,⟨⟨1,0,-4,1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],17⟩,⟨⟨0,-1,1,5⟩,[.t (0),.s,.t (5)],18⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],19⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],20⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],21⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],22⟩,⟨⟨1,1,-4,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],23⟩,⟨⟨-1,0,-5,-1⟩,[.t (0),.s,.t (-5),.s,.t (0)],24⟩,⟨⟨0,-1,1,-4⟩,[.t (0),.s,.t (-4)],25⟩,⟨⟨-1,1,-3,2⟩,[.t (0),.s,.t (-3),.s,.t (-1)],26⟩,⟨⟨1,2,2,5⟩,[.t (0),.s,.t (-2),.s,.t (2)],27⟩,⟨⟨-2,-1,7,3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],28⟩,⟨⟨1,-1,-3,4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2)],29⟩,⟨⟨-1,-2,4,7⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],30⟩,⟨⟨-1,-1,5,4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],31⟩,⟨⟨1,0,4,1⟩,[.t (0),.s,.t (-4),.s,.t (0)],32⟩,⟨⟨0,1,-1,3⟩,[.t (0),.s,.t (-3)],33⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],34⟩,⟨⟨2,-1,5,-2⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-1)],35⟩,⟨⟨-1,-3,-2,-7⟩,[.t (0),.s,.t (-2),.s,.t (3)],36⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],37⟩,⟨⟨-2,1,7,-4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-1)],38⟩,⟨⟨1,3,-4,-11⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (2)],39⟩,⟨⟨-1,1,4,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],40⟩,⟨⟨1,2,-5,-9⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],41⟩,⟨⟨-1,-1,-4,-5⟩,[.t (0),.s,.t (-4),.s,.t (1)],42⟩,⟨⟨1,1,3,4⟩,[.t (0),.s,.t (-3),.s,.t (1)],43⟩,⟨⟨2,1,5,3⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (0)],44⟩,⟨⟨-3,1,-7,2⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-1)],45⟩,⟨⟨1,4,2,9⟩,[.t (0),.s,.t (-2),.s,.t (4)],46⟩,⟨⟨1,-2,-2,5⟩,[.t (-1),.s,.t (-2),.s,.t (-3)],47⟩,⟨⟨-2,-3,5,7⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (1)],48⟩,⟨⟨5,3,13,8⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (0)],49⟩,⟨⟨-3,2,-8,5⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-1)],50⟩,⟨⟨2,1,9,5⟩,[.t (0),.s,.t (-5),.s,.t (-2),.s,.t (0)],51⟩,⟨⟨-1,1,-5,4⟩,[.t (0),.s,.t (-5),.s,.t (-1)],52⟩,⟨⟨1,2,4,9⟩,[.t (0),.s,.t (-4),.s,.t (2)],53⟩,⟨⟨-3,-1,-8,-3⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (0)],54⟩,⟨⟨1,-2,3,-5⟩,[.t (0),.s,.t (-3),.s,.t (-2)],55⟩,⟨⟨-2,-3,-5,-8⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (1)],56⟩,⟨⟨-3,-2,-7,-5⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],57⟩,⟨⟨4,1,-9,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-5),.s,.t (0)],58⟩,⟨⟨-1,3,2,-7⟩,[.t (-1),.s,.t (-2),.s,.t (-4)],59⟩,⟨⟨3,2,-11,-7⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],60⟩,⟨⟨2,1,-9,-4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],61⟩,⟨⟨2,5,5,13⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (2)],62⟩,⟨⟨-3,-1,7,2⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (0)],63⟩,⟨⟨4,3,9,7⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],64⟩,⟨⟨2,-3,-7,11⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],65⟩,⟨⟨-3,-5,11,18⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (1)],66⟩,⟨⟨5,-2,13,-5⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-1)],67⟩,⟨⟨-2,-7,-5,-18⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (3)],68⟩,⟨⟨3,4,-7,-9⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (1)],69⟩,⟨⟨-7,-5,-18,-13⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],70⟩,⟨⟨-5,-2,18,7⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (0)],71⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 72 ∧ ((List.finRange 72).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 72) := [⟨4,1,⟨⟨1,2,0,1⟩,[.t (2)],0⟩⟩,⟨12,2,⟨⟨3,2,4,3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨58,8,⟨⟨17,8,36,17⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨69,11,⟨⟨55,24,126,55⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨48,9,⟨⟨-29,-12,-70,-29⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨22,4,⟨⟨11,4,-36,-13⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨28,4,⟨⟨-13,-4,36,11⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨71,13,⟨⟨85,24,216,61⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨66,12,⟨⟨-167,-46,-432,-119⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨39,5,⟨⟨-53,-14,-140,-37⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-5),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨61,10,⟨⟨17,4,72,17⟩,[.t (0),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨41,6,⟨⟨-19,-4,-90,-19⟩,[.t (0),.s,.t (-5),.s,.t (-4),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨18,3,⟨⟨-1,0,-10,-1⟩,[.t (0),.s,.t (-10),.s,.t (0)],0⟩⟩,⟨24,3,⟨⟨-1,0,10,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨51,6,⟨⟨-19,4,90,-19⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨53,10,⟨⟨17,-4,-72,17⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨43,7,⟨⟨-13,4,-36,11⟩,[.t (0),.s,.t (-3),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨54,7,⟨⟨11,-4,36,-13⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨49,5,⟨⟨-37,14,140,-53⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨70,12,⟨⟨-119,46,432,-167⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨68,13,⟨⟨61,-24,-216,85⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-7),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨57,9,⟨⟨-29,12,70,-29⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨64,11,⟨⟨55,-24,-126,55⟩,[.t (-1),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-5),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨46,8,⟨⟨17,-8,-36,17⟩,[.t (-1),.s,.t (-2),.s,.t (-10),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨11,2,⟨⟨3,-2,-4,3⟩,[.t (-1),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨2,1,⟨⟨1,-2,0,1⟩,[.t (-2)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-1,2),(-4,9),(-3,7),(-2,5),(-1,3),(-2,7),(-5,18),(-3,11),(-1,4),(-2,9),(-1,5),(0,1),(1,5),(2,9),(1,4),(1,3),(3,8),(5,13),(7,18),(2,5),(3,7),(4,9),(1,2),(1,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G200_43_c0

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
