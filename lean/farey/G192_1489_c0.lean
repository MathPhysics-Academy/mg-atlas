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
namespace G192_1489_c0
noncomputable def originalSData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (10)) (.leaf (12)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (7))) (.branch 12 (.leaf (16)) (.leaf (8)))) (.branch 15 (.branch 14 (.leaf (18)) (.leaf (20))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (11)) (.leaf (24))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (13)) (.leaf (27))) (.branch 21 (.leaf (14)) (.leaf (15)))) (.branch 24 (.branch 23 (.leaf (29)) (.leaf (31))) (.branch 25 (.leaf (17)) (.branch 26 (.leaf (34)) (.leaf (35)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (19)) (.leaf (38))) (.branch 30 (.leaf (22)) (.leaf (40)))) (.branch 33 (.branch 32 (.leaf (23)) (.leaf (42))) (.branch 34 (.leaf (44)) (.branch 35 (.leaf (25)) (.leaf (26)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (37)) (.leaf (36))) (.branch 39 (.leaf (28)) (.leaf (48)))) (.branch 42 (.branch 41 (.leaf (30)) (.leaf (49))) (.branch 43 (.leaf (32)) (.branch 44 (.leaf (50)) (.leaf (33)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (52)) (.leaf (47))) (.branch 48 (.leaf (46)) (.leaf (39)))) (.branch 51 (.branch 50 (.leaf (41)) (.leaf (43))) (.branch 52 (.leaf (57)) (.branch 53 (.leaf (45)) (.leaf (54))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (53)) (.leaf (61))) (.branch 57 (.leaf (62)) (.leaf (51)))) (.branch 60 (.branch 59 (.leaf (65)) (.leaf (66))) (.branch 61 (.leaf (68)) (.branch 62 (.leaf (55)) (.leaf (56)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (64)) (.leaf (63))) (.branch 66 (.leaf (58)) (.leaf (59)))) (.branch 69 (.branch 68 (.leaf (71)) (.leaf (60))) (.branch 70 (.leaf (70)) (.branch 71 (.leaf (69)) (.leaf (67)))))))))
noncomputable def originalS (p : Fin 72) : Fin 72 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (13)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (14)) (.leaf (15))) (.branch 12 (.leaf (17)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (19)) (.leaf (21))) (.branch 16 (.leaf (22)) (.branch 17 (.leaf (23)) (.leaf (25))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (26)) (.leaf (28))) (.branch 21 (.leaf (4)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (30)) (.leaf (32))) (.branch 25 (.leaf (33)) (.branch 26 (.leaf (35)) (.leaf (36)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (37)) (.leaf (39))) (.branch 30 (.leaf (20)) (.leaf (41)))) (.branch 33 (.branch 32 (.leaf (10)) (.leaf (43))) (.branch 34 (.leaf (45)) (.branch 35 (.leaf (46)) (.leaf (12)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (18)) (.leaf (34))) (.branch 39 (.leaf (47)) (.leaf (29)))) (.branch 42 (.branch 41 (.leaf (48)) (.leaf (31))) (.branch 43 (.leaf (49)) (.branch 44 (.leaf (51)) (.leaf (16)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (53)) (.leaf (27))) (.branch 48 (.leaf (24)) (.leaf (54)))) (.branch 51 (.branch 50 (.leaf (55)) (.leaf (56))) (.branch 52 (.leaf (58)) (.branch 53 (.leaf (59)) (.leaf (38))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (60)) (.leaf (62))) (.branch 57 (.leaf (63)) (.leaf (64)))) (.branch 60 (.branch 59 (.leaf (66)) (.leaf (67))) (.branch 61 (.leaf (69)) (.branch 62 (.leaf (40)) (.leaf (42)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (50)) (.leaf (61))) (.branch 66 (.leaf (70)) (.leaf (44)))) (.branch 69 (.branch 68 (.leaf (68)) (.leaf (52))) (.branch 70 (.leaf (57)) (.branch 71 (.leaf (71)) (.leaf (65)))))))))
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
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.branch 8 (.leaf (10)) (.leaf (12)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (5)) (.leaf (7))) (.branch 12 (.leaf (16)) (.leaf (8)))) (.branch 15 (.branch 14 (.leaf (18)) (.leaf (20))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (11)) (.leaf (24))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (13)) (.leaf (27))) (.branch 21 (.leaf (14)) (.leaf (15)))) (.branch 24 (.branch 23 (.leaf (29)) (.leaf (31))) (.branch 25 (.leaf (17)) (.branch 26 (.leaf (34)) (.leaf (35)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (19)) (.leaf (38))) (.branch 30 (.leaf (22)) (.leaf (40)))) (.branch 33 (.branch 32 (.leaf (23)) (.leaf (42))) (.branch 34 (.leaf (44)) (.branch 35 (.leaf (25)) (.leaf (26)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (37)) (.leaf (36))) (.branch 39 (.leaf (28)) (.leaf (48)))) (.branch 42 (.branch 41 (.leaf (30)) (.leaf (49))) (.branch 43 (.leaf (32)) (.branch 44 (.leaf (50)) (.leaf (33)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (52)) (.leaf (47))) (.branch 48 (.leaf (46)) (.leaf (39)))) (.branch 51 (.branch 50 (.leaf (41)) (.leaf (43))) (.branch 52 (.leaf (57)) (.branch 53 (.leaf (45)) (.leaf (54))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (53)) (.leaf (61))) (.branch 57 (.leaf (62)) (.leaf (51)))) (.branch 60 (.branch 59 (.leaf (65)) (.leaf (66))) (.branch 61 (.leaf (68)) (.branch 62 (.leaf (55)) (.leaf (56)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (64)) (.leaf (63))) (.branch 66 (.leaf (58)) (.leaf (59)))) (.branch 69 (.branch 68 (.leaf (71)) (.leaf (60))) (.branch 70 (.leaf (70)) (.branch 71 (.leaf (69)) (.leaf (67)))))))))
noncomputable def S (p : Fin 72) : Fin 72 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (11)) (.leaf (13)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (14)) (.leaf (15))) (.branch 12 (.leaf (17)) (.leaf (1)))) (.branch 15 (.branch 14 (.leaf (19)) (.leaf (21))) (.branch 16 (.leaf (22)) (.branch 17 (.leaf (23)) (.leaf (25))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (26)) (.leaf (28))) (.branch 21 (.leaf (4)) (.leaf (6)))) (.branch 24 (.branch 23 (.leaf (30)) (.leaf (32))) (.branch 25 (.leaf (33)) (.branch 26 (.leaf (35)) (.leaf (36)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (37)) (.leaf (39))) (.branch 30 (.leaf (20)) (.leaf (41)))) (.branch 33 (.branch 32 (.leaf (10)) (.leaf (43))) (.branch 34 (.leaf (45)) (.branch 35 (.leaf (46)) (.leaf (12)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (18)) (.leaf (34))) (.branch 39 (.leaf (47)) (.leaf (29)))) (.branch 42 (.branch 41 (.leaf (48)) (.leaf (31))) (.branch 43 (.leaf (49)) (.branch 44 (.leaf (51)) (.leaf (16)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (53)) (.leaf (27))) (.branch 48 (.leaf (24)) (.leaf (54)))) (.branch 51 (.branch 50 (.leaf (55)) (.leaf (56))) (.branch 52 (.leaf (58)) (.branch 53 (.leaf (59)) (.leaf (38))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (60)) (.leaf (62))) (.branch 57 (.leaf (63)) (.leaf (64)))) (.branch 60 (.branch 59 (.leaf (66)) (.leaf (67))) (.branch 61 (.leaf (69)) (.branch 62 (.leaf (40)) (.leaf (42)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (50)) (.leaf (61))) (.branch 66 (.leaf (70)) (.leaf (44)))) (.branch 69 (.branch 68 (.leaf (68)) (.leaf (52))) (.branch 70 (.leaf (57)) (.branch 71 (.leaf (71)) (.leaf (65)))))))))
noncomputable def T (p : Fin 72) : Fin 72 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 72) :=
  (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (5)) (.leaf (12))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (20)) (.leaf (2))) (.branch 7 (.leaf (21)) (.branch 8 (.leaf (3)) (.leaf (4)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (31))) (.branch 12 (.leaf (7)) (.leaf (35)))) (.branch 15 (.branch 14 (.leaf (8)) (.leaf (9))) (.branch 16 (.leaf (10)) (.branch 17 (.leaf (44)) (.leaf (11))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (36)) (.leaf (13))) (.branch 21 (.leaf (29)) (.leaf (14)))) (.branch 24 (.branch 23 (.leaf (15)) (.leaf (16))) (.branch 25 (.leaf (47)) (.branch 26 (.leaf (17)) (.leaf (18)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (46)) (.leaf (19))) (.branch 30 (.leaf (39)) (.leaf (22)))) (.branch 33 (.branch 32 (.leaf (41)) (.leaf (23))) (.branch 34 (.leaf (24)) (.branch 35 (.leaf (37)) (.leaf (25)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (26)) (.leaf (27))) (.branch 39 (.leaf (53)) (.leaf (28)))) (.branch 42 (.branch 41 (.leaf (61)) (.leaf (30))) (.branch 43 (.leaf (62)) (.branch 44 (.leaf (32)) (.leaf (66)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (33)) (.leaf (34))) (.branch 48 (.leaf (38)) (.leaf (40)))) (.branch 51 (.branch 50 (.leaf (42)) (.leaf (63))) (.branch 52 (.leaf (43)) (.branch 53 (.leaf (68)) (.leaf (45))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (48)) (.leaf (49))) (.branch 57 (.leaf (50)) (.leaf (69)))) (.branch 60 (.branch 59 (.leaf (51)) (.leaf (52))) (.branch 61 (.leaf (54)) (.branch 62 (.leaf (64)) (.leaf (55)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (56)) (.leaf (57))) (.branch 66 (.leaf (71)) (.leaf (58)))) (.branch 69 (.branch 68 (.leaf (59)) (.leaf (67))) (.branch 70 (.leaf (60)) (.branch 71 (.leaf (65)) (.leaf (70)))))))))
noncomputable def Ti (p : Fin 72) : Fin 72 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 72) : Fin 72 := T (S p)
theorem quotient_relations : (∀ p : Fin 72, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 72, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 72, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 72, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 72)) := [[0,3,9],[1,2,8],[4,5,14],[6,7,15],[10,11,23],[12,13,26],[16,17,33],[18,19,37],[20,21,22],[24,25,46],[27,28,47],[29,30,48],[31,32,49],[34,35,36],[38,39,54],[40,41,55],[42,43,56],[44,45,59],[50,51,64],[52,53,60],[57,58,70],[61,62,63],[65,66,67],[68,69,71]]
noncomputable def verticesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (2)) (.leaf (12))) (.branch 12 (.leaf (13)) (.leaf (15)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (8))) (.branch 16 (.leaf (11)) (.branch 17 (.leaf (18)) (.leaf (19))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (21)) (.leaf (22))) (.branch 21 (.leaf (24)) (.leaf (25)))) (.branch 24 (.branch 23 (.leaf (26)) (.leaf (14))) (.branch 25 (.leaf (27)) (.branch 26 (.leaf (28)) (.leaf (17)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (30)) (.leaf (31))) (.branch 30 (.leaf (33)) (.leaf (34)))) (.branch 33 (.branch 32 (.leaf (36)) (.leaf (37))) (.branch 34 (.leaf (20)) (.branch 35 (.leaf (39)) (.leaf (40)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (41)) (.leaf (23))) (.branch 39 (.leaf (42)) (.leaf (43)))) (.branch 42 (.branch 41 (.leaf (45)) (.leaf (46))) (.branch 43 (.leaf (48)) (.branch 44 (.leaf (49)) (.leaf (51)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (52)) (.leaf (29))) (.branch 48 (.leaf (32)) (.leaf (35)))) (.branch 51 (.branch 50 (.leaf (38)) (.leaf (54))) (.branch 52 (.leaf (55)) (.branch 53 (.leaf (57)) (.leaf (58))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (44)) (.leaf (47))) (.branch 57 (.leaf (50)) (.leaf (60)))) (.branch 60 (.branch 59 (.leaf (61)) (.leaf (53))) (.branch 61 (.leaf (59)) (.branch 62 (.leaf (63)) (.leaf (64)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (65)) (.leaf (56))) (.branch 66 (.leaf (66)) (.leaf (67)))) (.branch 69 (.branch 68 (.leaf (68)) (.leaf (69))) (.branch 70 (.leaf (70)) (.branch 71 (.leaf (62)) (.leaf (71)))))))))
noncomputable def verticesIndex (p : Fin 72) : Fin 72 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (9)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (14)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (6)) (.leaf (7))) (.branch 12 (.leaf (15)) (.leaf (10)))) (.branch 15 (.branch 14 (.leaf (11)) (.leaf (23))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (26))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (16)) (.leaf (17))) (.branch 21 (.leaf (33)) (.leaf (18)))) (.branch 24 (.branch 23 (.leaf (19)) (.leaf (37))) (.branch 25 (.leaf (20)) (.branch 26 (.leaf (21)) (.leaf (22)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (24)) (.leaf (25))) (.branch 30 (.leaf (46)) (.leaf (27)))) (.branch 33 (.branch 32 (.leaf (28)) (.leaf (47))) (.branch 34 (.leaf (29)) (.branch 35 (.leaf (30)) (.leaf (48)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (31)) (.leaf (32))) (.branch 39 (.leaf (49)) (.leaf (34)))) (.branch 42 (.branch 41 (.leaf (35)) (.leaf (36))) (.branch 43 (.leaf (38)) (.branch 44 (.leaf (39)) (.leaf (54)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (40)) (.leaf (41))) (.branch 48 (.leaf (55)) (.leaf (42)))) (.branch 51 (.branch 50 (.leaf (43)) (.leaf (56))) (.branch 52 (.leaf (44)) (.branch 53 (.leaf (45)) (.leaf (59))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (50)) (.leaf (51))) (.branch 57 (.leaf (64)) (.leaf (52)))) (.branch 60 (.branch 59 (.leaf (53)) (.leaf (60))) (.branch 61 (.leaf (57)) (.branch 62 (.leaf (58)) (.leaf (70)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (61)) (.leaf (62))) (.branch 66 (.leaf (63)) (.leaf (65)))) (.branch 69 (.branch 68 (.leaf (66)) (.leaf (67))) (.branch 70 (.leaf (68)) (.branch 71 (.leaf (69)) (.leaf (71)))))))))
noncomputable def verticesBack (p : Fin 72) : Fin 72 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 72, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 72 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 72, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 72)) := [[0,1],[2,4],[3,6],[5,9],[7,10],[8,12],[11,16],[13,18],[14,20],[15,21],[17,24],[19,27],[22,29],[23,31],[25,34],[26,35],[28,38],[30,40],[32,42],[33,44],[36,37],[39,48],[41,49],[43,50],[45,52],[46,47],[51,57],[53,54],[55,61],[56,62],[58,65],[59,66],[60,68],[63,64],[67,71],[69,70]]
noncomputable def edgesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (10)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (7)) (.leaf (9))) (.branch 12 (.leaf (12)) (.leaf (11)))) (.branch 15 (.branch 14 (.leaf (14)) (.leaf (16))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (13)) (.leaf (20))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (15)) (.leaf (22))) (.branch 21 (.leaf (17)) (.leaf (19)))) (.branch 24 (.branch 23 (.leaf (24)) (.leaf (26))) (.branch 25 (.leaf (21)) (.branch 26 (.leaf (28)) (.leaf (30)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (23)) (.leaf (32))) (.branch 30 (.leaf (25)) (.leaf (34)))) (.branch 33 (.branch 32 (.leaf (27)) (.leaf (36))) (.branch 34 (.leaf (38)) (.branch 35 (.leaf (29)) (.leaf (31)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (40)) (.leaf (41))) (.branch 39 (.leaf (33)) (.leaf (42)))) (.branch 42 (.branch 41 (.leaf (35)) (.leaf (44))) (.branch 43 (.leaf (37)) (.branch 44 (.leaf (46)) (.leaf (39)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (48)) (.leaf (50))) (.branch 48 (.leaf (51)) (.leaf (43)))) (.branch 51 (.branch 50 (.leaf (45)) (.leaf (47))) (.branch 52 (.leaf (52)) (.branch 53 (.leaf (49)) (.leaf (54))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (55)) (.leaf (56))) (.branch 57 (.leaf (58)) (.leaf (53)))) (.branch 60 (.branch 59 (.leaf (60)) (.leaf (62))) (.branch 61 (.leaf (64)) (.branch 62 (.leaf (57)) (.leaf (59)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (66)) (.leaf (67))) (.branch 66 (.leaf (61)) (.leaf (63)))) (.branch 69 (.branch 68 (.leaf (68)) (.leaf (65))) (.branch 70 (.leaf (70)) (.branch 71 (.leaf (71)) (.leaf (69)))))))))
noncomputable def edgesIndex (p : Fin 72) : Fin 72 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (10)) (.leaf (8))) (.branch 12 (.leaf (12)) (.leaf (11)))) (.branch 15 (.branch 14 (.leaf (16)) (.leaf (13))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (14)) (.leaf (20))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (15)) (.leaf (21))) (.branch 21 (.leaf (17)) (.leaf (24)))) (.branch 24 (.branch 23 (.leaf (19)) (.leaf (27))) (.branch 25 (.leaf (22)) (.branch 26 (.leaf (29)) (.leaf (23)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (31)) (.leaf (25))) (.branch 30 (.leaf (34)) (.leaf (26)))) (.branch 33 (.branch 32 (.leaf (35)) (.leaf (28))) (.branch 34 (.leaf (38)) (.branch 35 (.leaf (30)) (.leaf (40)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (32)) (.leaf (42))) (.branch 39 (.leaf (33)) (.leaf (44)))) (.branch 42 (.branch 41 (.leaf (36)) (.leaf (37))) (.branch 43 (.leaf (39)) (.branch 44 (.leaf (48)) (.leaf (41)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (49)) (.leaf (43))) (.branch 48 (.leaf (50)) (.leaf (45)))) (.branch 51 (.branch 50 (.leaf (52)) (.leaf (46))) (.branch 52 (.leaf (47)) (.branch 53 (.leaf (51)) (.leaf (57))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (53)) (.leaf (54))) (.branch 57 (.leaf (55)) (.leaf (61)))) (.branch 60 (.branch 59 (.leaf (56)) (.leaf (62))) (.branch 61 (.leaf (58)) (.branch 62 (.leaf (65)) (.leaf (59)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (66)) (.leaf (60))) (.branch 66 (.leaf (68)) (.leaf (63)))) (.branch 69 (.branch 68 (.leaf (64)) (.leaf (67))) (.branch 70 (.leaf (71)) (.branch 71 (.leaf (69)) (.leaf (70)))))))))
noncomputable def edgesBack (p : Fin 72) : Fin 72 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 72, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 72 := by decide +kernel
theorem edges_partition : ∀ p : Fin 72, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 72)) := [[0,2,5],[1,3,7,11,17,25,35,12],[4,8,13,19,28,39,29,20],[6,9,14,21],[10,15,22,30,41,31],[16,23,32,43,51,58,66,44],[18,26,36],[24,33,45,53,38,47],[27,37,34,46],[40,48,54,60,69,57,64,61],[42,49,55,62],[50,56,63],[52,59,67,68],[65,70,71]]
noncomputable def facesIndexData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (11)) (.leaf (2))) (.branch 7 (.leaf (19)) (.branch 8 (.leaf (5)) (.leaf (12)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (20)) (.leaf (23))) (.branch 12 (.leaf (6)) (.leaf (10)))) (.branch 15 (.branch 14 (.leaf (13)) (.leaf (21))) (.branch 16 (.leaf (24)) (.branch 17 (.leaf (29)) (.leaf (7))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (37)) (.leaf (14))) (.branch 21 (.leaf (18)) (.leaf (22)))) (.branch 24 (.branch 23 (.leaf (25)) (.leaf (30))) (.branch 25 (.leaf (40)) (.branch 26 (.leaf (8)) (.leaf (38)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (46)) (.leaf (15))) (.branch 30 (.leaf (17)) (.leaf (26)))) (.branch 33 (.branch 32 (.leaf (28)) (.leaf (31))) (.branch 34 (.leaf (41)) (.branch 35 (.leaf (48)) (.leaf (9)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (39)) (.leaf (47))) (.branch 39 (.leaf (44)) (.leaf (16)))) (.branch 42 (.branch 41 (.leaf (50)) (.leaf (27))) (.branch 43 (.leaf (58)) (.branch 44 (.leaf (32)) (.leaf (36)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (42)) (.leaf (49))) (.branch 48 (.leaf (45)) (.leaf (51)))) (.branch 51 (.branch 50 (.leaf (59)) (.leaf (62))) (.branch 52 (.leaf (33)) (.branch 53 (.leaf (65)) (.leaf (43))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (52)) (.leaf (60))) (.branch 57 (.leaf (63)) (.leaf (55)))) (.branch 60 (.branch 59 (.leaf (34)) (.leaf (66))) (.branch 61 (.leaf (53)) (.branch 62 (.leaf (57)) (.leaf (61)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (64)) (.leaf (56))) (.branch 66 (.leaf (69)) (.leaf (35)))) (.branch 69 (.branch 68 (.leaf (67)) (.leaf (68))) (.branch 70 (.leaf (54)) (.branch 71 (.leaf (70)) (.leaf (71)))))))))
noncomputable def facesIndex (p : Fin 72) : Fin 72 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 72) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (7))) (.branch 7 (.leaf (11)) (.branch 8 (.leaf (17)) (.leaf (25)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (35)) (.leaf (12))) (.branch 12 (.leaf (4)) (.leaf (8)))) (.branch 15 (.branch 14 (.leaf (13)) (.leaf (19))) (.branch 16 (.leaf (28)) (.branch 17 (.leaf (39)) (.leaf (29))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (20)) (.leaf (6))) (.branch 21 (.leaf (9)) (.leaf (14)))) (.branch 24 (.branch 23 (.leaf (21)) (.leaf (10))) (.branch 25 (.leaf (15)) (.branch 26 (.leaf (22)) (.leaf (30)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (41)) (.leaf (31))) (.branch 30 (.leaf (16)) (.leaf (23)))) (.branch 33 (.branch 32 (.leaf (32)) (.leaf (43))) (.branch 34 (.leaf (51)) (.branch 35 (.leaf (58)) (.leaf (66)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (44)) (.leaf (18))) (.branch 39 (.leaf (26)) (.leaf (36)))) (.branch 42 (.branch 41 (.leaf (24)) (.leaf (33))) (.branch 43 (.leaf (45)) (.branch 44 (.leaf (53)) (.leaf (38)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (47)) (.leaf (27))) (.branch 48 (.leaf (37)) (.leaf (34)))) (.branch 51 (.branch 50 (.leaf (46)) (.leaf (40))) (.branch 52 (.leaf (48)) (.branch 53 (.leaf (54)) (.leaf (60))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (69)) (.leaf (57))) (.branch 57 (.leaf (64)) (.leaf (61)))) (.branch 60 (.branch 59 (.leaf (42)) (.leaf (49))) (.branch 61 (.leaf (55)) (.branch 62 (.leaf (62)) (.leaf (50)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (56)) (.leaf (63))) (.branch 66 (.leaf (52)) (.leaf (59)))) (.branch 69 (.branch 68 (.leaf (67)) (.leaf (68))) (.branch 70 (.leaf (65)) (.branch 71 (.leaf (70)) (.leaf (71)))))))))
noncomputable def facesBack (p : Fin 72) : Fin 72 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 72, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 72 := by decide +kernel
theorem faces_partition : ∀ p : Fin 72, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [3,8,8,4,6,8,3,6,4,8,4,3,4,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 0 : Int) = 24 - 36 + 14 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 36 (.branch 18 (.branch 9 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))))) (.branch 13 (.branch 11 (.branch 10 (.leaf (⟨-1,-1,1,0⟩)) (.leaf (⟨1,0,-2,1⟩))) (.branch 12 (.leaf (⟨0,-1,1,3⟩)) (.leaf (⟨0,1,-1,1⟩)))) (.branch 15 (.branch 14 (.leaf (⟨1,1,1,2⟩)) (.leaf (⟨2,1,1,1⟩))) (.branch 16 (.leaf (⟨1,1,-2,-1⟩)) (.branch 17 (.leaf (⟨-1,0,3,-1⟩)) (.leaf (⟨0,1,-1,-4⟩))))))) (.branch 27 (.branch 22 (.branch 20 (.branch 19 (.leaf (⟨1,-1,2,-1⟩)) (.leaf (⟨-1,-2,-1,-3⟩))) (.branch 21 (.leaf (⟨1,-2,1,-1⟩)) (.leaf (⟨-2,-3,-1,-2⟩)))) (.branch 24 (.branch 23 (.leaf (⟨-3,-1,-2,-1⟩)) (.leaf (⟨-1,-1,3,2⟩))) (.branch 25 (.leaf (⟨1,0,4,1⟩)) (.branch 26 (.leaf (⟨0,1,-1,3⟩)) (.leaf (⟨1,0,2,1⟩)))))) (.branch 31 (.branch 29 (.branch 28 (.leaf (⟨-2,1,-3,1⟩)) (.leaf (⟨1,3,1,4⟩))) (.branch 30 (.leaf (⟨-1,3,-1,2⟩)) (.leaf (⟨3,4,2,3⟩)))) (.branch 33 (.branch 32 (.leaf (⟨-1,1,2,-3⟩)) (.leaf (⟨1,2,-3,-5⟩))) (.branch 34 (.leaf (⟨1,1,-4,-3⟩)) (.branch 35 (.leaf (⟨-1,0,-3,-1⟩)) (.leaf (⟨0,-1,1,-2⟩)))))))) (.branch 54 (.branch 45 (.branch 40 (.branch 38 (.branch 37 (.leaf (⟨-1,-1,-2,-3⟩)) (.leaf (⟨-2,-1,-3,-2⟩))) (.branch 39 (.leaf (⟨-5,-1,-4,-1⟩)) (.leaf (⟨1,-4,1,-3⟩)))) (.branch 42 (.branch 41 (.leaf (⟨4,-3,3,-2⟩)) (.leaf (⟨-3,-7,-2,-5⟩))) (.branch 43 (.leaf (⟨2,-1,-5,3⟩)) (.branch 44 (.leaf (⟨-1,-3,3,8⟩)) (.leaf (⟨1,-1,-3,4⟩)))))) (.branch 49 (.branch 47 (.branch 46 (.leaf (⟨-1,-2,4,7⟩)) (.leaf (⟨1,1,3,4⟩))) (.branch 48 (.leaf (⟨3,2,4,3⟩)) (.leaf (⟨4,1,3,1⟩)))) (.branch 51 (.branch 50 (.leaf (⟨2,1,-5,-2⟩)) (.leaf (⟨-3,1,8,-3⟩))) (.branch 52 (.leaf (⟨1,4,-3,-11⟩)) (.branch 53 (.leaf (⟨9,5,7,4⟩)) (.leaf (⟨-5,4,-4,3⟩))))))) (.branch 63 (.branch 58 (.branch 56 (.branch 55 (.leaf (⟨-4,-5,-3,-4⟩)) (.leaf (⟨-7,-4,-5,-3⟩))) (.branch 57 (.leaf (⟨-3,-2,8,5⟩)) (.leaf (⟨-4,-1,13,3⟩)))) (.branch 60 (.branch 59 (.leaf (⟨1,-3,-3,10⟩)) (.leaf (⟨-2,-1,7,3⟩))) (.branch 61 (.leaf (⟨4,9,3,7⟩)) (.branch 62 (.leaf (⟨-4,7,-3,5⟩)) (.leaf (⟨7,11,5,8⟩)))))) (.branch 67 (.branch 65 (.branch 64 (.leaf (⟨11,4,8,3⟩)) (.leaf (⟨4,3,-11,-8⟩))) (.branch 66 (.leaf (⟨3,1,-10,-3⟩)) (.leaf (⟨-1,2,3,-7⟩)))) (.branch 69 (.branch 68 (.leaf (⟨2,3,-7,-10⟩)) (.leaf (⟨9,-4,7,-3⟩))) (.branch 70 (.leaf (⟨-4,-13,-3,-10⟩)) (.branch 71 (.leaf (⟨-3,-4,10,13⟩)) (.leaf (⟨-13,-9,-10,-7⟩)))))))))
noncomputable def liftMatrix (p : Fin 72) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 72) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],10⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],11⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],12⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],13⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],14⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],15⟩,⟨⟨-1,0,3,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],16⟩,⟨⟨0,1,-1,-4⟩,[.t (0),.s,.t (4)],17⟩,⟨⟨1,-1,2,-1⟩,[.t (0),.s,.t (-2),.s,.t (-1)],18⟩,⟨⟨-1,-2,-1,-3⟩,[.t (1),.s,.t (3)],19⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],20⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],21⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],22⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],23⟩,⟨⟨1,0,4,1⟩,[.t (0),.s,.t (-4),.s,.t (0)],24⟩,⟨⟨0,1,-1,3⟩,[.t (0),.s,.t (-3)],25⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],26⟩,⟨⟨-2,1,-3,1⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-1)],27⟩,⟨⟨1,3,1,4⟩,[.t (1),.s,.t (4)],28⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],29⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],30⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],31⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],32⟩,⟨⟨1,1,-4,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],33⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],34⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],35⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],36⟩,⟨⟨-2,-1,-3,-2⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (0)],37⟩,⟨⟨-5,-1,-4,-1⟩,[.t (1),.s,.t (-4),.s,.t (0)],38⟩,⟨⟨1,-4,1,-3⟩,[.t (1),.s,.t (-3)],39⟩,⟨⟨4,-3,3,-2⟩,[.t (1),.s,.t (-3),.s,.t (-1)],40⟩,⟨⟨-3,-7,-2,-5⟩,[.t (1),.s,.t (-2),.s,.t (2)],41⟩,⟨⟨2,-1,-5,3⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-1)],42⟩,⟨⟨-1,-3,3,8⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (2)],43⟩,⟨⟨1,-1,-3,4⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2)],44⟩,⟨⟨-1,-2,4,7⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (1)],45⟩,⟨⟨1,1,3,4⟩,[.t (0),.s,.t (-3),.s,.t (1)],46⟩,⟨⟨3,2,4,3⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],47⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],48⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],49⟩,⟨⟨-3,1,8,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],50⟩,⟨⟨1,4,-3,-11⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (3)],51⟩,⟨⟨9,5,7,4⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (0)],52⟩,⟨⟨-5,4,-4,3⟩,[.t (1),.s,.t (-4),.s,.t (-1)],53⟩,⟨⟨-4,-5,-3,-4⟩,[.t (1),.s,.t (-3),.s,.t (1)],54⟩,⟨⟨-7,-4,-5,-3⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (0)],55⟩,⟨⟨-3,-2,8,5⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],56⟩,⟨⟨-4,-1,13,3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (0)],57⟩,⟨⟨1,-3,-3,10⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-4)],58⟩,⟨⟨-2,-1,7,3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],59⟩,⟨⟨4,9,3,7⟩,[.t (1),.s,.t (-3),.s,.t (2)],60⟩,⟨⟨-4,7,-3,5⟩,[.t (1),.s,.t (-3),.s,.t (-2)],61⟩,⟨⟨7,11,5,8⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (1)],62⟩,⟨⟨11,4,8,3⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (0)],63⟩,⟨⟨4,3,-11,-8⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],64⟩,⟨⟨3,1,-10,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (0)],65⟩,⟨⟨-1,2,3,-7⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3)],66⟩,⟨⟨2,3,-7,-10⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (1)],67⟩,⟨⟨9,-4,7,-3⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-1)],68⟩,⟨⟨-4,-13,-3,-10⟩,[.t (1),.s,.t (-3),.s,.t (3)],69⟩,⟨⟨-3,-4,10,13⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (1)],70⟩,⟨⟨-13,-9,-10,-7⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (0)],71⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 72 ∧ ((List.finRange 72).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 72) := [⟨9,1,⟨⟨-1,-3,0,-1⟩,[.t (3)],0⟩⟩,⟨15,2,⟨⟨7,5,4,3⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨49,6,⟨⟨-29,-13,-20,-9⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨56,10,⟨⟨111,43,80,31⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨64,11,⟨⟨153,56,112,41⟩,[.t (1),.s,.t (-3),.s,.t (-4),.s,.t (-4),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨51,9,⟨⟨23,8,-72,-25⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-9),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨57,9,⟨⟨-25,-8,72,23⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨70,13,⟨⟨209,64,160,49⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨67,12,⟨⟨181,53,140,41⟩,[.t (1),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨45,7,⟨⟨71,19,56,15⟩,[.t (1),.s,.t (-4),.s,.t (-4),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨17,3,⟨⟨-1,0,-8,-1⟩,[.t (0),.s,.t (-8),.s,.t (0)],0⟩⟩,⟨24,3,⟨⟨-1,0,8,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨46,8,⟨⟨17,-5,24,-7⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨36,5,⟨⟨7,-3,12,-5⟩,[.t (0),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨37,5,⟨⟨-5,3,-12,7⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨47,8,⟨⟨-7,5,-24,17⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨28,4,⟨⟨-9,8,-8,7⟩,[.t (1),.s,.t (-8),.s,.t (-1)],0⟩⟩,⟨38,4,⟨⟨7,-8,8,-9⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨52,7,⟨⟨15,-19,-56,71⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨71,12,⟨⟨41,-53,-140,181⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨69,13,⟨⟨49,-64,-160,209⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-5),.s,.t (-5),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨63,11,⟨⟨41,-56,-112,153⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨62,10,⟨⟨31,-43,-80,111⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨41,6,⟨⟨-9,13,20,-29⟩,[.t (-1),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨21,2,⟨⟨3,-5,-4,7⟩,[.t (-1),.s,.t (-4),.s,.t (-2)],0⟩⟩,⟨5,1,⟨⟨-1,3,0,-1⟩,[.t (-3)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-1,2),(-2,5),(-3,8),(-4,11),(-1,3),(-4,13),(-3,10),(-2,7),(-1,4),(0,1),(1,4),(1,3),(1,2),(2,3),(3,4),(1,1),(5,4),(9,7),(13,10),(4,3),(11,8),(7,5),(3,2),(2,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11,12,13]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G192_1489_c0

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
