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
namespace G144_116_c0
noncomputable def originalSData : LookupTree (Fin 96) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (9)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (12)) (.branch 8 (.leaf (0)) (.leaf (15)))) (.branch 10 (.leaf (14)) (.branch 11 (.leaf (18)) (.leaf (20)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (16)) (.branch 14 (.leaf (17)) (.leaf (23)))) (.branch 16 (.leaf (2)) (.branch 17 (.leaf (26)) (.leaf (27))))) (.branch 21 (.branch 19 (.leaf (24)) (.branch 20 (.leaf (30)) (.leaf (25)))) (.branch 22 (.leaf (32)) (.branch 23 (.leaf (33)) (.leaf (4))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (36)) (.branch 26 (.leaf (38)) (.leaf (6)))) (.branch 28 (.leaf (35)) (.branch 29 (.leaf (41)) (.leaf (42))))) (.branch 33 (.branch 31 (.leaf (37)) (.branch 32 (.leaf (45)) (.leaf (39)))) (.branch 34 (.leaf (40)) (.branch 35 (.leaf (48)) (.leaf (13)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (10)) (.branch 38 (.leaf (52)) (.leaf (11)))) (.branch 40 (.leaf (54)) (.branch 41 (.leaf (55)) (.leaf (50))))) (.branch 45 (.branch 43 (.leaf (51)) (.branch 44 (.leaf (31)) (.leaf (58)))) (.branch 46 (.leaf (53)) (.branch 47 (.leaf (28)) (.leaf (61)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (56)) (.branch 50 (.leaf (63)) (.leaf (46)))) (.branch 52 (.leaf (65)) (.branch 53 (.leaf (19)) (.leaf (43))))) (.branch 57 (.branch 55 (.leaf (21)) (.branch 56 (.leaf (22)) (.leaf (68)))) (.branch 58 (.leaf (70)) (.branch 59 (.leaf (66)) (.leaf (72)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (73)) (.branch 62 (.leaf (67)) (.leaf (75)))) (.branch 64 (.leaf (69)) (.branch 65 (.leaf (47)) (.leaf (29))))) (.branch 69 (.branch 67 (.leaf (78)) (.branch 68 (.leaf (64)) (.leaf (34)))) (.branch 70 (.leaf (81)) (.branch 71 (.leaf (60)) (.leaf (82))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (79)) (.branch 74 (.leaf (57)) (.leaf (85)))) (.branch 76 (.leaf (80)) (.branch 77 (.leaf (84)) (.leaf (83))))) (.branch 81 (.branch 79 (.leaf (44)) (.branch 80 (.leaf (88)) (.leaf (89)))) (.branch 82 (.leaf (49)) (.branch 83 (.leaf (74)) (.leaf (91)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (90)) (.branch 86 (.leaf (71)) (.leaf (77)))) (.branch 88 (.leaf (93)) (.branch 89 (.leaf (59)) (.leaf (62))))) (.branch 93 (.branch 91 (.leaf (94)) (.branch 92 (.leaf (86)) (.leaf (87)))) (.branch 94 (.leaf (95)) (.branch 95 (.leaf (76)) (.leaf (92)))))))))
noncomputable def originalS (p : Fin 96) : Fin 96 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 96) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (4)) (.leaf (6)))) (.branch 4 (.leaf (8)) (.branch 5 (.leaf (10)) (.leaf (11))))) (.branch 9 (.branch 7 (.leaf (13)) (.branch 8 (.leaf (14)) (.leaf (16)))) (.branch 10 (.leaf (17)) (.branch 11 (.leaf (19)) (.leaf (21)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (22)) (.branch 14 (.leaf (0)) (.leaf (24)))) (.branch 16 (.leaf (25)) (.branch 17 (.leaf (27)) (.leaf (28))))) (.branch 21 (.branch 19 (.leaf (29)) (.branch 20 (.leaf (31)) (.leaf (1)))) (.branch 22 (.leaf (33)) (.branch 23 (.leaf (34)) (.leaf (35))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (37)) (.branch 26 (.leaf (39)) (.leaf (40)))) (.branch 28 (.leaf (3)) (.branch 29 (.leaf (42)) (.leaf (43))))) (.branch 33 (.branch 31 (.leaf (44)) (.branch 32 (.leaf (46)) (.leaf (47)))) (.branch 34 (.leaf (5)) (.branch 35 (.leaf (49)) (.leaf (50)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (51)) (.branch 38 (.leaf (53)) (.leaf (7)))) (.branch 40 (.leaf (55)) (.branch 41 (.leaf (56)) (.leaf (12))))) (.branch 45 (.branch 43 (.leaf (9)) (.branch 44 (.leaf (57)) (.leaf (59)))) (.branch 46 (.leaf (60)) (.branch 47 (.leaf (26)) (.leaf (62)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (54)) (.branch 50 (.leaf (64)) (.leaf (65)))) (.branch 52 (.leaf (45)) (.branch 53 (.leaf (66)) (.leaf (41))))) (.branch 57 (.branch 55 (.leaf (67)) (.branch 56 (.leaf (15)) (.leaf (69)))) (.branch 58 (.leaf (71)) (.branch 59 (.leaf (18)) (.leaf (73)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (74)) (.branch 62 (.leaf (20)) (.leaf (76)))) (.branch 64 (.leaf (77)) (.branch 65 (.leaf (38)) (.leaf (23))))) (.branch 69 (.branch 67 (.leaf (79)) (.branch 68 (.leaf (80)) (.leaf (32)))) (.branch 70 (.leaf (61)) (.branch 71 (.leaf (52)) (.leaf (83))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (84)) (.branch 74 (.leaf (30)) (.leaf (86)))) (.branch 76 (.leaf (63)) (.branch 77 (.leaf (78)) (.leaf (87))))) (.branch 81 (.branch 79 (.leaf (36)) (.branch 80 (.leaf (70)) (.leaf (90)))) (.branch 82 (.leaf (91)) (.branch 83 (.leaf (72)) (.leaf (48)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (92)) (.branch 86 (.leaf (88)) (.leaf (68)))) (.branch 88 (.leaf (75)) (.branch 89 (.leaf (94)) (.leaf (81))))) (.branch 93 (.branch 91 (.leaf (58)) (.branch 92 (.leaf (95)) (.leaf (82)))) (.branch 94 (.leaf (85)) (.branch 95 (.leaf (93)) (.leaf (89)))))))))
noncomputable def originalT (p : Fin 96) : Fin 96 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 48) :=
  (.branch 48 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (0)) (.branch 5 (.leaf (3)) (.leaf (4))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (1)) (.leaf (2)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (8)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (3)))) (.branch 16 (.leaf (4)) (.branch 17 (.leaf (5)) (.leaf (11))))) (.branch 21 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (13)) (.leaf (14)))) (.branch 22 (.leaf (15)) (.branch 23 (.leaf (16)) (.leaf (6))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (7)) (.branch 26 (.leaf (8)) (.leaf (9)))) (.branch 28 (.leaf (10)) (.branch 29 (.leaf (17)) (.leaf (18))))) (.branch 33 (.branch 31 (.leaf (19)) (.branch 32 (.leaf (20)) (.leaf (21)))) (.branch 34 (.leaf (22)) (.branch 35 (.leaf (23)) (.leaf (11)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (12)) (.branch 38 (.leaf (13)) (.leaf (14)))) (.branch 40 (.leaf (15)) (.branch 41 (.leaf (16)) (.leaf (24))))) (.branch 45 (.branch 43 (.leaf (25)) (.branch 44 (.leaf (26)) (.leaf (27)))) (.branch 46 (.leaf (26)) (.branch 47 (.leaf (24)) (.leaf (28)))))))) (.branch 72 (.branch 60 (.branch 54 (.branch 51 (.branch 49 (.leaf (29)) (.branch 50 (.leaf (30)) (.leaf (17)))) (.branch 52 (.leaf (18)) (.branch 53 (.leaf (19)) (.leaf (20))))) (.branch 57 (.branch 55 (.leaf (21)) (.branch 56 (.leaf (22)) (.leaf (23)))) (.branch 58 (.leaf (31)) (.branch 59 (.leaf (32)) (.leaf (33)))))) (.branch 66 (.branch 63 (.branch 61 (.leaf (31)) (.branch 62 (.leaf (34)) (.leaf (35)))) (.branch 64 (.leaf (36)) (.branch 65 (.leaf (34)) (.leaf (25))))) (.branch 69 (.branch 67 (.leaf (27)) (.branch 68 (.leaf (28)) (.leaf (29)))) (.branch 70 (.leaf (30)) (.branch 71 (.leaf (37)) (.leaf (38))))))) (.branch 84 (.branch 78 (.branch 75 (.branch 73 (.leaf (39)) (.branch 74 (.leaf (37)) (.leaf (38)))) (.branch 76 (.leaf (40)) (.branch 77 (.leaf (41)) (.leaf (42))))) (.branch 81 (.branch 79 (.leaf (32)) (.branch 80 (.leaf (33)) (.leaf (35)))) (.branch 82 (.leaf (36)) (.branch 83 (.leaf (43)) (.leaf (44)))))) (.branch 90 (.branch 87 (.branch 85 (.leaf (45)) (.branch 86 (.leaf (43)) (.leaf (44)))) (.branch 88 (.leaf (46)) (.branch 89 (.leaf (39)) (.leaf (40))))) (.branch 93 (.branch 91 (.leaf (41)) (.branch 92 (.leaf (42)) (.leaf (47)))) (.branch 94 (.leaf (47)) (.branch 95 (.leaf (45)) (.leaf (46)))))))))
noncomputable def projection (p : Fin 96) : Fin 48 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 96) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (5)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (11)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (13)) (.leaf (17)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (18)) (.branch 14 (.leaf (19)) (.leaf (20)))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (22)) (.leaf (28))))) (.branch 21 (.branch 19 (.leaf (29)) (.branch 20 (.leaf (30)) (.leaf (31)))) (.branch 22 (.leaf (32)) (.branch 23 (.leaf (33)) (.leaf (34))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (41)) (.branch 26 (.leaf (42)) (.leaf (43)))) (.branch 28 (.leaf (44)) (.branch 29 (.leaf (47)) (.leaf (48))))) (.branch 33 (.branch 31 (.leaf (49)) (.branch 32 (.leaf (57)) (.leaf (58)))) (.branch 34 (.leaf (59)) (.branch 35 (.leaf (61)) (.leaf (62)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (63)) (.branch 38 (.leaf (70)) (.leaf (71)))) (.branch 40 (.leaf (72)) (.branch 41 (.leaf (75)) (.leaf (76))))) (.branch 45 (.branch 43 (.leaf (77)) (.branch 44 (.leaf (82)) (.leaf (83)))) (.branch 46 (.leaf (84)) (.branch 47 (.leaf (87)) (.leaf (92))))))))
noncomputable def representative (p : Fin 48) : Fin 96 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (1)) (.branch 2 (.leaf (0)) (.leaf (4)))) (.branch 4 (.leaf (6)) (.branch 5 (.leaf (2)) (.leaf (9))))) (.branch 9 (.branch 7 (.leaf (3)) (.branch 8 (.leaf (12)) (.leaf (14)))) (.branch 10 (.leaf (5)) (.branch 11 (.leaf (11)) (.leaf (10)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (7)) (.branch 14 (.leaf (19)) (.leaf (8)))) (.branch 16 (.leaf (21)) (.branch 17 (.leaf (22)) (.leaf (24))))) (.branch 21 (.branch 19 (.leaf (25)) (.branch 20 (.leaf (13)) (.leaf (26)))) (.branch 22 (.leaf (15)) (.branch 23 (.leaf (16)) (.leaf (29))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (17)) (.branch 26 (.leaf (18)) (.leaf (20)))) (.branch 28 (.leaf (32)) (.branch 29 (.leaf (34)) (.leaf (23))))) (.branch 33 (.branch 31 (.leaf (36)) (.branch 32 (.leaf (37)) (.leaf (27)))) (.branch 34 (.leaf (39)) (.branch 35 (.leaf (28)) (.leaf (40)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (30)) (.branch 38 (.leaf (31)) (.leaf (43)))) (.branch 40 (.leaf (33)) (.branch 41 (.leaf (35)) (.leaf (45))))) (.branch 45 (.branch 43 (.leaf (44)) (.branch 44 (.leaf (38)) (.leaf (42)))) (.branch 46 (.leaf (41)) (.branch 47 (.leaf (47)) (.leaf (46))))))))
noncomputable def S (p : Fin 48) : Fin 48 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (2)) (.branch 2 (.leaf (3)) (.leaf (5)))) (.branch 4 (.leaf (7)) (.branch 5 (.leaf (8)) (.leaf (10))))) (.branch 9 (.branch 7 (.leaf (11)) (.branch 8 (.leaf (13)) (.leaf (15)))) (.branch 10 (.leaf (16)) (.branch 11 (.leaf (0)) (.leaf (17)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (18)) (.branch 14 (.leaf (20)) (.leaf (1)))) (.branch 16 (.leaf (22)) (.branch 17 (.leaf (23)) (.leaf (25))))) (.branch 21 (.branch 19 (.leaf (26)) (.branch 20 (.leaf (27)) (.leaf (24)))) (.branch 22 (.leaf (28)) (.branch 23 (.leaf (4)) (.leaf (30))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (9)) (.branch 26 (.leaf (6)) (.leaf (31)))) (.branch 28 (.leaf (33)) (.branch 29 (.leaf (35)) (.leaf (21))))) (.branch 33 (.branch 31 (.leaf (34)) (.branch 32 (.leaf (38)) (.leaf (12)))) (.branch 34 (.leaf (37)) (.branch 35 (.leaf (14)) (.leaf (41)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (42)) (.branch 38 (.leaf (19)) (.leaf (44)))) (.branch 40 (.leaf (45)) (.branch 41 (.leaf (36)) (.leaf (32))))) (.branch 45 (.branch 43 (.leaf (46)) (.branch 44 (.leaf (39)) (.leaf (29)))) (.branch 46 (.leaf (47)) (.branch 47 (.leaf (40)) (.leaf (43))))))))
noncomputable def T (p : Fin 48) : Fin 48 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 48) :=
  (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (10)) (.branch 2 (.leaf (14)) (.leaf (0)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (22)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (25)) (.branch 8 (.leaf (3)) (.leaf (4)))) (.branch 10 (.leaf (24)) (.branch 11 (.leaf (5)) (.leaf (6)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (32)) (.branch 14 (.leaf (7)) (.leaf (34)))) (.branch 16 (.leaf (8)) (.branch 17 (.leaf (9)) (.leaf (11))))) (.branch 21 (.branch 19 (.leaf (12)) (.branch 20 (.leaf (37)) (.leaf (13)))) (.branch 22 (.leaf (29)) (.branch 23 (.leaf (15)) (.leaf (16))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (20)) (.branch 26 (.leaf (17)) (.leaf (18)))) (.branch 28 (.leaf (19)) (.branch 29 (.leaf (21)) (.leaf (44))))) (.branch 33 (.branch 31 (.leaf (23)) (.branch 32 (.leaf (26)) (.leaf (41)))) (.branch 34 (.leaf (27)) (.branch 35 (.leaf (30)) (.leaf (28)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (40)) (.branch 38 (.leaf (33)) (.leaf (31)))) (.branch 40 (.leaf (43)) (.branch 41 (.leaf (46)) (.leaf (35))))) (.branch 45 (.branch 43 (.leaf (36)) (.branch 44 (.leaf (47)) (.leaf (38)))) (.branch 46 (.leaf (39)) (.branch 47 (.leaf (42)) (.leaf (45))))))))
noncomputable def Ti (p : Fin 48) : Fin 48 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 48) : Fin 48 := T (S p)
theorem quotient_relations : (∀ p : Fin 48, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 96, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 96, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 48, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 48)) := [[0,3,11],[1,2,8],[4,5,16],[6,7,18],[9,10,17],[12,13,27],[14,15,28],[19,20,31],[21,22,23],[24,25,26],[29,30,42],[32,33,45],[34,35,36],[37,38,39],[40,41,47],[43,44,46]]
noncomputable def verticesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (4)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (6)) (.leaf (7))))) (.branch 9 (.branch 7 (.leaf (9)) (.branch 8 (.leaf (10)) (.leaf (5)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (13)) (.leaf (2)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (15)) (.branch 14 (.leaf (16)) (.leaf (18)))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (8)) (.leaf (14))))) (.branch 21 (.branch 19 (.leaf (11)) (.branch 20 (.leaf (21)) (.leaf (22)))) (.branch 22 (.leaf (24)) (.branch 23 (.leaf (25)) (.leaf (26))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (27)) (.branch 26 (.leaf (28)) (.leaf (29)))) (.branch 28 (.leaf (17)) (.branch 29 (.leaf (20)) (.leaf (30))))) (.branch 33 (.branch 31 (.leaf (31)) (.branch 32 (.leaf (23)) (.leaf (33)))) (.branch 34 (.leaf (34)) (.branch 35 (.leaf (36)) (.leaf (37)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (38)) (.branch 38 (.leaf (39)) (.leaf (40)))) (.branch 40 (.leaf (41)) (.branch 41 (.leaf (42)) (.leaf (43))))) (.branch 45 (.branch 43 (.leaf (32)) (.branch 44 (.leaf (45)) (.leaf (46)))) (.branch 46 (.leaf (35)) (.branch 47 (.leaf (47)) (.leaf (44))))))))
noncomputable def verticesIndex (p : Fin 48) : Fin 48 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (3)) (.leaf (11)))) (.branch 4 (.leaf (1)) (.branch 5 (.leaf (2)) (.leaf (8))))) (.branch 9 (.branch 7 (.leaf (4)) (.branch 8 (.leaf (5)) (.leaf (16)))) (.branch 10 (.leaf (6)) (.branch 11 (.leaf (7)) (.leaf (18)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (10)) (.leaf (17)))) (.branch 16 (.leaf (12)) (.branch 17 (.leaf (13)) (.leaf (27))))) (.branch 21 (.branch 19 (.leaf (14)) (.branch 20 (.leaf (15)) (.leaf (28)))) (.branch 22 (.leaf (19)) (.branch 23 (.leaf (20)) (.leaf (31))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (21)) (.branch 26 (.leaf (22)) (.leaf (23)))) (.branch 28 (.leaf (24)) (.branch 29 (.leaf (25)) (.leaf (26))))) (.branch 33 (.branch 31 (.leaf (29)) (.branch 32 (.leaf (30)) (.leaf (42)))) (.branch 34 (.leaf (32)) (.branch 35 (.leaf (33)) (.leaf (45)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (34)) (.branch 38 (.leaf (35)) (.leaf (36)))) (.branch 40 (.leaf (37)) (.branch 41 (.leaf (38)) (.leaf (39))))) (.branch 45 (.branch 43 (.leaf (40)) (.branch 44 (.leaf (41)) (.leaf (47)))) (.branch 46 (.leaf (43)) (.branch 47 (.leaf (44)) (.leaf (46))))))))
noncomputable def verticesBack (p : Fin 48) : Fin 48 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 48, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 48 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 48, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 48)) := [[0,1],[2,4],[3,6],[5,9],[7,12],[8,14],[10,11],[13,19],[15,21],[16,22],[17,24],[18,25],[20,26],[23,29],[27,32],[28,34],[30,36],[31,37],[33,39],[35,40],[38,43],[41,45],[42,44],[46,47]]
noncomputable def edgesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (8)) (.leaf (10)))) (.branch 10 (.leaf (7)) (.branch 11 (.leaf (12)) (.leaf (13)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (9)) (.branch 14 (.leaf (14)) (.leaf (11)))) (.branch 16 (.leaf (16)) (.branch 17 (.leaf (18)) (.leaf (20))))) (.branch 21 (.branch 19 (.leaf (22)) (.branch 20 (.leaf (15)) (.leaf (24)))) (.branch 22 (.leaf (17)) (.branch 23 (.leaf (19)) (.leaf (26))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (21)) (.branch 26 (.leaf (23)) (.leaf (25)))) (.branch 28 (.leaf (28)) (.branch 29 (.leaf (30)) (.leaf (27))))) (.branch 33 (.branch 31 (.leaf (32)) (.branch 32 (.leaf (34)) (.leaf (29)))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (31)) (.leaf (38)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (33)) (.branch 38 (.leaf (35)) (.leaf (40)))) (.branch 40 (.leaf (37)) (.branch 41 (.leaf (39)) (.leaf (42))))) (.branch 45 (.branch 43 (.leaf (44)) (.branch 44 (.leaf (41)) (.leaf (45)))) (.branch 46 (.leaf (43)) (.branch 47 (.leaf (46)) (.leaf (47))))))))
noncomputable def edgesIndex (p : Fin 48) : Fin 48 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (1)) (.leaf (2)))) (.branch 4 (.leaf (4)) (.branch 5 (.leaf (3)) (.leaf (6))))) (.branch 9 (.branch 7 (.leaf (5)) (.branch 8 (.leaf (9)) (.leaf (7)))) (.branch 10 (.leaf (12)) (.branch 11 (.leaf (8)) (.leaf (14)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (10)) (.branch 14 (.leaf (11)) (.leaf (13)))) (.branch 16 (.leaf (19)) (.branch 17 (.leaf (15)) (.leaf (21))))) (.branch 21 (.branch 19 (.leaf (16)) (.branch 20 (.leaf (22)) (.leaf (17)))) (.branch 22 (.leaf (24)) (.branch 23 (.leaf (18)) (.leaf (25))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (20)) (.branch 26 (.leaf (26)) (.leaf (23)))) (.branch 28 (.leaf (29)) (.branch 29 (.leaf (27)) (.leaf (32))))) (.branch 33 (.branch 31 (.leaf (28)) (.branch 32 (.leaf (34)) (.leaf (30)))) (.branch 34 (.leaf (36)) (.branch 35 (.leaf (31)) (.leaf (37)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (33)) (.branch 38 (.leaf (39)) (.leaf (35)))) (.branch 40 (.leaf (40)) (.branch 41 (.leaf (38)) (.leaf (43))))) (.branch 45 (.branch 43 (.leaf (41)) (.branch 44 (.leaf (45)) (.leaf (42)))) (.branch 46 (.leaf (44)) (.branch 47 (.leaf (46)) (.leaf (47))))))))
noncomputable def edgesBack (p : Fin 48) : Fin 48 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 48, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 48 := by decide +kernel
theorem edges_partition : ∀ p : Fin 48, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 48)) := [[0,2,5,10],[1,3,7,13,20,24,9,16,23,30,34,14],[4,8,15,22],[6,11,17,25],[12,18,26,31,38,44,29,21,28,35,41,32],[19,27,33,37],[36,42,46,40],[39,45,47,43]]
noncomputable def facesIndexData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (4)) (.leaf (1)))) (.branch 4 (.leaf (5)) (.branch 5 (.leaf (16)) (.leaf (2))))) (.branch 9 (.branch 7 (.leaf (20)) (.branch 8 (.leaf (6)) (.leaf (17)))) (.branch 10 (.leaf (10)) (.branch 11 (.leaf (3)) (.leaf (21)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (24)) (.branch 14 (.leaf (7)) (.leaf (15)))) (.branch 16 (.leaf (18)) (.branch 17 (.leaf (11)) (.leaf (22))))) (.branch 21 (.branch 19 (.leaf (25)) (.branch 20 (.leaf (36)) (.leaf (8)))) (.branch 22 (.leaf (31)) (.branch 23 (.leaf (19)) (.leaf (12))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (9)) (.branch 26 (.leaf (23)) (.leaf (26)))) (.branch 28 (.leaf (37)) (.branch 29 (.leaf (32)) (.leaf (30))))) (.branch 33 (.branch 31 (.leaf (13)) (.branch 32 (.leaf (27)) (.leaf (35)))) (.branch 34 (.leaf (38)) (.branch 35 (.leaf (14)) (.leaf (33)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (40)) (.branch 38 (.leaf (39)) (.leaf (28)))) (.branch 40 (.leaf (44)) (.branch 41 (.leaf (43)) (.leaf (34))))) (.branch 45 (.branch 43 (.leaf (41)) (.branch 44 (.leaf (47)) (.leaf (29)))) (.branch 46 (.leaf (45)) (.branch 47 (.leaf (42)) (.leaf (46))))))))
noncomputable def facesIndex (p : Fin 48) : Fin 48 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 48) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (0)) (.branch 2 (.leaf (2)) (.leaf (5)))) (.branch 4 (.leaf (10)) (.branch 5 (.leaf (1)) (.leaf (3))))) (.branch 9 (.branch 7 (.leaf (7)) (.branch 8 (.leaf (13)) (.leaf (20)))) (.branch 10 (.leaf (24)) (.branch 11 (.leaf (9)) (.leaf (16)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (23)) (.branch 14 (.leaf (30)) (.leaf (34)))) (.branch 16 (.leaf (14)) (.branch 17 (.leaf (4)) (.leaf (8))))) (.branch 21 (.branch 19 (.leaf (15)) (.branch 20 (.leaf (22)) (.leaf (6)))) (.branch 22 (.leaf (11)) (.branch 23 (.leaf (17)) (.leaf (25))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (12)) (.branch 26 (.leaf (18)) (.leaf (26)))) (.branch 28 (.leaf (31)) (.branch 29 (.leaf (38)) (.leaf (44))))) (.branch 33 (.branch 31 (.leaf (29)) (.branch 32 (.leaf (21)) (.leaf (28)))) (.branch 34 (.leaf (35)) (.branch 35 (.leaf (41)) (.leaf (32)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (19)) (.branch 38 (.leaf (27)) (.leaf (33)))) (.branch 40 (.leaf (37)) (.branch 41 (.leaf (36)) (.leaf (42))))) (.branch 45 (.branch 43 (.leaf (46)) (.branch 44 (.leaf (40)) (.leaf (39)))) (.branch 46 (.leaf (45)) (.branch 47 (.leaf (47)) (.leaf (43))))))))
noncomputable def facesBack (p : Fin 48) : Fin 48 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 48, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 48 := by decide +kernel
theorem faces_partition : ∀ p : Fin 48, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [4,12,4,4,12,4,4,4] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 1 : Int) = 16 - 24 + 8 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 0 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 24 (.branch 12 (.branch 6 (.branch 3 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.branch 2 (.leaf (⟨0,-1,1,0⟩)) (.leaf (⟨-1,-1,0,-1⟩)))) (.branch 4 (.leaf (⟨0,-1,1,1⟩)) (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))))) (.branch 9 (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.branch 8 (.leaf (⟨0,1,-1,-2⟩)) (.leaf (⟨-1,0,-1,-1⟩)))) (.branch 10 (.leaf (⟨2,-1,1,0⟩)) (.branch 11 (.leaf (⟨-1,-3,0,-1⟩)) (.leaf (⟨-1,-1,1,0⟩)))))) (.branch 18 (.branch 15 (.branch 13 (.leaf (⟨1,0,-2,1⟩)) (.branch 14 (.leaf (⟨0,-1,1,3⟩)) (.leaf (⟨0,1,-1,1⟩)))) (.branch 16 (.leaf (⟨1,1,1,2⟩)) (.branch 17 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨-3,-2,-1,-1⟩))))) (.branch 21 (.branch 19 (.leaf (⟨1,1,-2,-1⟩)) (.branch 20 (.leaf (⟨-7,-2,-3,-1⟩)) (.leaf (⟨2,-5,1,-2⟩)))) (.branch 22 (.leaf (⟨-3,-1,-2,-1⟩)) (.branch 23 (.leaf (⟨1,-2,1,-1⟩)) (.leaf (⟨-2,-3,-1,-2⟩))))))) (.branch 36 (.branch 30 (.branch 27 (.branch 25 (.leaf (⟨-2,3,-1,1⟩)) (.branch 26 (.leaf (⟨3,5,1,2⟩)) (.leaf (⟨5,2,2,1⟩)))) (.branch 28 (.leaf (⟨-1,-1,3,2⟩)) (.branch 29 (.leaf (⟨1,0,2,1⟩)) (.leaf (⟨-3,2,-2,1⟩))))) (.branch 33 (.branch 31 (.leaf (⟨2,5,1,3⟩)) (.branch 32 (.leaf (⟨-5,-7,-2,-3⟩)) (.leaf (⟨-1,1,2,-3⟩)))) (.branch 34 (.leaf (⟨1,2,-3,-5⟩)) (.branch 35 (.leaf (⟨0,-1,1,-2⟩)) (.leaf (⟨-1,-1,-2,-3⟩)))))) (.branch 42 (.branch 39 (.branch 37 (.leaf (⟨-1,0,-3,-1⟩)) (.branch 38 (.leaf (⟨-7,5,-3,2⟩)) (.leaf (⟨5,12,2,5⟩)))) (.branch 40 (.leaf (⟨12,7,5,3⟩)) (.branch 41 (.leaf (⟨-1,1,-3,2⟩)) (.leaf (⟨1,2,2,5⟩))))) (.branch 45 (.branch 43 (.leaf (⟨5,3,3,2⟩)) (.branch 44 (.leaf (⟨-8,-3,-5,-2⟩)) (.leaf (⟨3,-5,2,-3⟩)))) (.branch 46 (.leaf (⟨2,1,-5,-2⟩)) (.branch 47 (.leaf (⟨-5,-8,-3,-5⟩)) (.leaf (⟨2,1,5,3⟩))))))))
noncomputable def liftMatrix (p : Fin 48) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 48) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨2,-1,1,0⟩,[.t (2),.s,.t (0)],9⟩,⟨⟨-1,-3,0,-1⟩,[.t (3)],10⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],11⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],12⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],13⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],14⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],15⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],16⟩,⟨⟨-3,-2,-1,-1⟩,[.t (3),.s,.t (1)],17⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],18⟩,⟨⟨-7,-2,-3,-1⟩,[.t (2),.s,.t (-3),.s,.t (0)],19⟩,⟨⟨2,-5,1,-2⟩,[.t (2),.s,.t (-2)],20⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],21⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],22⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],23⟩,⟨⟨-2,3,-1,1⟩,[.t (2),.s,.t (-1)],24⟩,⟨⟨3,5,1,2⟩,[.t (3),.s,.t (2)],25⟩,⟨⟨5,2,2,1⟩,[.t (2),.s,.t (-2),.s,.t (0)],26⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],27⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],28⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],29⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],30⟩,⟨⟨-5,-7,-2,-3⟩,[.t (2),.s,.t (-2),.s,.t (1)],31⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],32⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],33⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],34⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],35⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],36⟩,⟨⟨-7,5,-3,2⟩,[.t (2),.s,.t (-3),.s,.t (-1)],37⟩,⟨⟨5,12,2,5⟩,[.t (2),.s,.t (-2),.s,.t (2)],38⟩,⟨⟨12,7,5,3⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (0)],39⟩,⟨⟨-1,1,-3,2⟩,[.t (0),.s,.t (-3),.s,.t (-1)],40⟩,⟨⟨1,2,2,5⟩,[.t (0),.s,.t (-2),.s,.t (2)],41⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],42⟩,⟨⟨-8,-3,-5,-2⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (0)],43⟩,⟨⟨3,-5,2,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2)],44⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],45⟩,⟨⟨-5,-8,-3,-5⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (1)],46⟩,⟨⟨2,1,5,3⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (0)],47⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 48 ∧ ((List.finRange 48).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 48) := [⟨11,1,⟨⟨1,4,0,1⟩,[.t (4)],0⟩⟩,⟨18,4,⟨⟨-11,-8,-4,-3⟩,[.t (2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨45,8,⟨⟨9,4,20,9⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨33,6,⟨⟨-71,-26,-30,-11⟩,[.t (2),.s,.t (-3),.s,.t (-4),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨13,2,⟨⟨-13,-2,-6,-1⟩,[.t (2),.s,.t (-6),.s,.t (0)],0⟩⟩,⟨36,5,⟨⟨11,-2,6,-1⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨47,9,⟨⟨49,-18,30,-11⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨41,8,⟨⟨9,-4,-20,9⟩,[.t (-1),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨15,3,⟨⟨-5,4,-4,3⟩,[.t (1),.s,.t (-4),.s,.t (-1)],0⟩⟩,⟨21,3,⟨⟨3,-4,4,-5⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨43,7,⟨⟨49,-76,20,-31⟩,[.t (2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨46,9,⟨⟨-11,18,-30,49⟩,[.t (0),.s,.t (-3),.s,.t (-4),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨30,5,⟨⟨-1,2,-6,11⟩,[.t (0),.s,.t (-6),.s,.t (-2)],0⟩⟩,⟨19,2,⟨⟨-1,2,6,-13⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨39,6,⟨⟨-11,26,30,-71⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨38,7,⟨⟨-31,76,-20,49⟩,[.t (1),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-3)],0⟩⟩,⟨25,4,⟨⟨-3,8,4,-11⟩,[.t (-1),.s,.t (-4),.s,.t (-3)],0⟩⟩,⟨10,1,⟨⟨1,-4,0,1⟩,[.t (-4)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-1,2),(-2,5),(-1,3),(0,1),(1,3),(2,5),(1,2),(1,1),(3,2),(8,5),(5,3),(2,1),(7,3),(12,5),(5,2),(3,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G144_116_c0

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
