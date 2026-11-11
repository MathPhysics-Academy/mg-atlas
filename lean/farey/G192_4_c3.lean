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
namespace G192_4_c3
noncomputable def originalSData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (9)) (.leaf (8))) (.branch 7 (.leaf (12)) (.leaf (0))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (13))) (.branch 11 (.leaf (16)) (.leaf (18)))) (.branch 14 (.branch 13 (.leaf (15)) (.leaf (21))) (.branch 15 (.leaf (2)) (.leaf (24)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (22)) (.leaf (26))) (.branch 19 (.leaf (23)) (.leaf (28)))) (.branch 22 (.branch 21 (.leaf (30)) (.leaf (4))) (.branch 23 (.leaf (32)) (.leaf (34))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (6)) (.leaf (37))) (.branch 27 (.leaf (33)) (.leaf (39)))) (.branch 30 (.branch 29 (.leaf (35)) (.leaf (42))) (.branch 31 (.leaf (36)) (.leaf (44))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (10)) (.leaf (47))) (.branch 35 (.leaf (11)) (.leaf (49)))) (.branch 38 (.branch 37 (.leaf (51)) (.leaf (46))) (.branch 39 (.leaf (53)) (.leaf (48))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (56)) (.leaf (57))) (.branch 43 (.leaf (50)) (.leaf (60)))) (.branch 46 (.branch 45 (.leaf (52)) (.leaf (62))) (.branch 47 (.leaf (64)) (.leaf (17)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (66)) (.leaf (19))) (.branch 51 (.leaf (69)) (.leaf (20)))) (.branch 54 (.branch 53 (.leaf (71)) (.leaf (65))) (.branch 55 (.leaf (73)) (.leaf (54))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (67)) (.leaf (68))) (.branch 59 (.leaf (76)) (.leaf (78)))) (.branch 62 (.branch 61 (.leaf (70)) (.leaf (43))) (.branch 63 (.leaf (72)) (.leaf (82)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (25)) (.leaf (84))) (.branch 67 (.leaf (27)) (.leaf (86)))) (.branch 70 (.branch 69 (.leaf (87)) (.leaf (29))) (.branch 71 (.leaf (61)) (.leaf (31))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (77)) (.leaf (85))) (.branch 75 (.leaf (92)) (.leaf (59)))) (.branch 78 (.branch 77 (.leaf (88)) (.leaf (45))) (.branch 79 (.leaf (89)) (.leaf (93)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (96)) (.leaf (98))) (.branch 83 (.leaf (90)) (.leaf (97)))) (.branch 86 (.branch 85 (.leaf (38)) (.leaf (55))) (.branch 87 (.leaf (40)) (.leaf (41))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (101)) (.leaf (75))) (.branch 91 (.leaf (102)) (.leaf (100)))) (.branch 94 (.branch 93 (.leaf (91)) (.leaf (80))) (.branch 95 (.leaf (104)) (.leaf (83))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (79)) (.leaf (103))) (.branch 99 (.leaf (94)) (.leaf (108)))) (.branch 102 (.branch 101 (.leaf (74)) (.leaf (58))) (.branch 103 (.leaf (63)) (.leaf (95))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (81)) (.leaf (110))) (.branch 107 (.leaf (112)) (.leaf (114)))) (.branch 110 (.branch 109 (.leaf (105)) (.leaf (117))) (.branch 111 (.leaf (99)) (.leaf (119)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (107)) (.leaf (120))) (.branch 115 (.leaf (106)) (.leaf (122)))) (.branch 118 (.branch 117 (.leaf (123)) (.leaf (111))) (.branch 119 (.leaf (121)) (.leaf (109))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (115)) (.leaf (116))) (.branch 123 (.leaf (113)) (.leaf (118)))) (.branch 126 (.branch 125 (.leaf (127)) (.leaf (124))) (.branch 127 (.leaf (125)) (.leaf (126)))))))))
noncomputable def originalS (p : Fin 128) : Fin 128 :=
  tableLookup originalSData p.val
noncomputable def originalTData : LookupTree (Fin 128) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (4))) (.branch 3 (.leaf (6)) (.leaf (8)))) (.branch 6 (.branch 5 (.leaf (10)) (.leaf (11))) (.branch 7 (.leaf (0)) (.leaf (13))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (15)) (.leaf (12))) (.branch 11 (.leaf (17)) (.leaf (19)))) (.branch 14 (.branch 13 (.leaf (20)) (.leaf (22))) (.branch 15 (.leaf (23)) (.leaf (3)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (25)) (.leaf (27))) (.branch 19 (.leaf (1)) (.leaf (29)))) (.branch 22 (.branch 21 (.leaf (31)) (.leaf (24))) (.branch 23 (.leaf (33)) (.leaf (35))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (36)) (.leaf (37))) (.branch 27 (.leaf (38)) (.leaf (40)))) (.branch 30 (.branch 29 (.leaf (41)) (.leaf (43))) (.branch 31 (.leaf (5)) (.leaf (45))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (46)) (.leaf (48))) (.branch 35 (.leaf (7)) (.leaf (50)))) (.branch 38 (.branch 37 (.leaf (52)) (.leaf (9))) (.branch 39 (.leaf (54)) (.leaf (55))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (57)) (.leaf (58))) (.branch 43 (.leaf (59)) (.leaf (30)))) (.branch 46 (.branch 45 (.leaf (61)) (.leaf (63))) (.branch 47 (.leaf (64)) (.leaf (65)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (67)) (.leaf (68))) (.branch 51 (.leaf (70)) (.leaf (14)))) (.branch 54 (.branch 53 (.leaf (72)) (.leaf (16))) (.branch 55 (.leaf (26)) (.leaf (74))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (75)) (.leaf (18))) (.branch 59 (.leaf (77)) (.leaf (39)))) (.branch 62 (.branch 61 (.leaf (79)) (.leaf (80))) (.branch 63 (.leaf (81)) (.leaf (83)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (21)) (.leaf (85))) (.branch 67 (.leaf (73)) (.leaf (87)))) (.branch 70 (.branch 69 (.leaf (88)) (.leaf (89))) (.branch 71 (.leaf (51)) (.leaf (60))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (90)) (.leaf (91))) (.branch 75 (.leaf (93)) (.leaf (49)))) (.branch 78 (.branch 77 (.leaf (86)) (.leaf (94))) (.branch 79 (.leaf (28)) (.leaf (95)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (97)) (.leaf (99))) (.branch 83 (.leaf (76)) (.leaf (100)))) (.branch 86 (.branch 85 (.leaf (32)) (.leaf (47))) (.branch 87 (.leaf (78)) (.leaf (34))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (62)) (.leaf (66))) (.branch 91 (.leaf (103)) (.leaf (96)))) (.branch 94 (.branch 93 (.leaf (84)) (.leaf (42))) (.branch 95 (.leaf (105)) (.leaf (106))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (69)) (.leaf (107))) (.branch 99 (.leaf (44)) (.leaf (109)))) (.branch 102 (.branch 101 (.leaf (53)) (.leaf (56))) (.branch 103 (.leaf (101)) (.leaf (92))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (71)) (.leaf (111))) (.branch 107 (.leaf (113)) (.leaf (115)))) (.branch 110 (.branch 109 (.leaf (116)) (.leaf (112))) (.branch 111 (.leaf (118)) (.leaf (114)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (102)) (.leaf (121))) (.branch 115 (.leaf (82)) (.leaf (123)))) (.branch 118 (.branch 117 (.leaf (124)) (.leaf (125))) (.branch 119 (.leaf (126)) (.leaf (127))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (119)) (.leaf (104))) (.branch 123 (.leaf (117)) (.leaf (98)))) (.branch 126 (.branch 125 (.leaf (108)) (.leaf (122))) (.branch 127 (.leaf (110)) (.leaf (120)))))))))
noncomputable def originalT (p : Fin 128) : Fin 128 :=
  tableLookup originalTData p.val
noncomputable def projectionData : LookupTree (Fin 64) :=
  (.branch 64 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (0)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (4))) (.branch 7 (.leaf (5)) (.leaf (1))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (2)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (8)))) (.branch 14 (.branch 13 (.leaf (9)) (.leaf (3))) (.branch 15 (.leaf (4)) (.leaf (5)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (10)) (.leaf (11))) (.branch 19 (.leaf (12)) (.leaf (13)))) (.branch 22 (.branch 21 (.leaf (14)) (.leaf (6))) (.branch 23 (.leaf (7)) (.leaf (8))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (9)) (.leaf (15))) (.branch 27 (.leaf (16)) (.leaf (17)))) (.branch 30 (.branch 29 (.leaf (18)) (.leaf (19))) (.branch 31 (.leaf (20)) (.leaf (21))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (10)) (.leaf (11))) (.branch 35 (.leaf (12)) (.leaf (13)))) (.branch 38 (.branch 37 (.leaf (14)) (.leaf (22))) (.branch 39 (.leaf (23)) (.leaf (24))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (25)) (.leaf (26))) (.branch 43 (.leaf (27)) (.leaf (28)))) (.branch 46 (.branch 45 (.leaf (29)) (.leaf (30))) (.branch 47 (.leaf (15)) (.leaf (16)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (17)) (.leaf (18))) (.branch 51 (.leaf (19)) (.leaf (20)))) (.branch 54 (.branch 53 (.leaf (21)) (.leaf (31))) (.branch 55 (.leaf (32)) (.leaf (33))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (34)) (.leaf (35))) (.branch 59 (.leaf (36)) (.leaf (37)))) (.branch 62 (.branch 61 (.leaf (38)) (.leaf (38))) (.branch 63 (.leaf (39)) (.leaf (40)))))))) (.branch 96 (.branch 80 (.branch 72 (.branch 68 (.branch 66 (.branch 65 (.leaf (22)) (.leaf (23))) (.branch 67 (.leaf (24)) (.leaf (25)))) (.branch 70 (.branch 69 (.leaf (26)) (.leaf (27))) (.branch 71 (.leaf (28)) (.leaf (29))))) (.branch 76 (.branch 74 (.branch 73 (.leaf (30)) (.leaf (33))) (.branch 75 (.leaf (41)) (.leaf (42)))) (.branch 78 (.branch 77 (.leaf (43)) (.leaf (39))) (.branch 79 (.leaf (42)) (.leaf (44)))))) (.branch 88 (.branch 84 (.branch 82 (.branch 81 (.leaf (44)) (.leaf (45))) (.branch 83 (.leaf (46)) (.leaf (47)))) (.branch 86 (.branch 85 (.leaf (31)) (.leaf (32))) (.branch 87 (.leaf (34)) (.leaf (35))))) (.branch 92 (.branch 90 (.branch 89 (.leaf (36)) (.leaf (37))) (.branch 91 (.leaf (40)) (.leaf (41)))) (.branch 94 (.branch 93 (.leaf (48)) (.leaf (49))) (.branch 95 (.leaf (45)) (.leaf (50))))))) (.branch 112 (.branch 104 (.branch 100 (.branch 98 (.branch 97 (.leaf (49)) (.leaf (50))) (.branch 99 (.leaf (51)) (.leaf (52)))) (.branch 102 (.branch 101 (.leaf (48)) (.leaf (43))) (.branch 103 (.leaf (46)) (.leaf (47))))) (.branch 108 (.branch 106 (.branch 105 (.leaf (51)) (.leaf (52))) (.branch 107 (.leaf (53)) (.leaf (53)))) (.branch 110 (.branch 109 (.leaf (54)) (.leaf (55))) (.branch 111 (.leaf (54)) (.leaf (55)))))) (.branch 120 (.branch 116 (.branch 114 (.branch 113 (.leaf (56)) (.leaf (57))) (.branch 115 (.leaf (56)) (.leaf (57)))) (.branch 118 (.branch 117 (.leaf (58)) (.leaf (59))) (.branch 119 (.leaf (58)) (.leaf (59))))) (.branch 124 (.branch 122 (.branch 121 (.leaf (60)) (.leaf (61))) (.branch 123 (.leaf (60)) (.leaf (61)))) (.branch 126 (.branch 125 (.leaf (62)) (.leaf (63))) (.branch 127 (.leaf (62)) (.leaf (63)))))))))
noncomputable def projection (p : Fin 128) : Fin 64 :=
  tableLookup projectionData p.val
noncomputable def representativeData : LookupTree (Fin 128) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (5)) (.leaf (6))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (11)) (.leaf (12))) (.branch 11 (.leaf (16)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (18)) (.leaf (19))) (.branch 15 (.leaf (20)) (.leaf (25)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (26)) (.leaf (27))) (.branch 19 (.leaf (28)) (.leaf (29)))) (.branch 22 (.branch 21 (.leaf (30)) (.leaf (31))) (.branch 23 (.leaf (37)) (.leaf (38))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (39)) (.leaf (40))) (.branch 27 (.leaf (41)) (.leaf (42)))) (.branch 30 (.branch 29 (.leaf (43)) (.leaf (44))) (.branch 31 (.leaf (45)) (.leaf (53))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (54)) (.leaf (55))) (.branch 35 (.leaf (56)) (.leaf (57)))) (.branch 38 (.branch 37 (.leaf (58)) (.leaf (59))) (.branch 39 (.leaf (60)) (.leaf (62))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (63)) (.leaf (74))) (.branch 43 (.leaf (75)) (.leaf (76)))) (.branch 46 (.branch 45 (.leaf (79)) (.leaf (81))) (.branch 47 (.leaf (82)) (.leaf (83)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (92)) (.leaf (93))) (.branch 51 (.leaf (95)) (.leaf (98)))) (.branch 54 (.branch 53 (.leaf (99)) (.leaf (106))) (.branch 55 (.leaf (108)) (.leaf (109))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (112)) (.leaf (113))) (.branch 59 (.leaf (116)) (.leaf (117)))) (.branch 62 (.branch 61 (.leaf (120)) (.leaf (121))) (.branch 63 (.leaf (124)) (.leaf (125))))))))
noncomputable def representative (p : Fin 64) : Fin 128 :=
  tableLookup representativeData p.val
noncomputable def SData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (1)) (.leaf (0))) (.branch 3 (.leaf (4)) (.leaf (6)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (9))) (.branch 7 (.leaf (3)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (5))) (.branch 11 (.leaf (7)) (.leaf (16)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (18))) (.branch 15 (.leaf (20)) (.leaf (22)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (11)) (.leaf (24))) (.branch 19 (.leaf (13)) (.leaf (27)))) (.branch 22 (.branch 21 (.leaf (14)) (.leaf (29))) (.branch 23 (.leaf (15)) (.leaf (31))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (17)) (.leaf (34))) (.branch 27 (.leaf (35)) (.leaf (19)))) (.branch 30 (.branch 29 (.leaf (38)) (.leaf (21))) (.branch 31 (.leaf (39)) (.leaf (23))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (33)) (.leaf (32))) (.branch 35 (.leaf (25)) (.leaf (26)))) (.branch 38 (.branch 37 (.leaf (43)) (.leaf (42))) (.branch 39 (.leaf (28)) (.leaf (30))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (46)) (.leaf (48))) (.branch 43 (.leaf (37)) (.leaf (36)))) (.branch 46 (.branch 45 (.leaf (49)) (.leaf (51))) (.branch 47 (.leaf (40)) (.leaf (50)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (41)) (.leaf (44))) (.branch 51 (.leaf (47)) (.leaf (45)))) (.branch 54 (.branch 53 (.leaf (54)) (.leaf (56))) (.branch 55 (.leaf (52)) (.leaf (59))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (53)) (.leaf (60))) (.branch 59 (.leaf (61)) (.leaf (55)))) (.branch 62 (.branch 61 (.leaf (57)) (.leaf (58))) (.branch 63 (.leaf (63)) (.leaf (62))))))))
noncomputable def S (p : Fin 64) : Fin 64 :=
  tableLookup SData p.val
noncomputable def TData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (2)) (.leaf (3))) (.branch 3 (.leaf (5)) (.leaf (7)))) (.branch 6 (.branch 5 (.leaf (8)) (.leaf (0))) (.branch 7 (.leaf (9)) (.leaf (11))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (13)) (.leaf (14))) (.branch 11 (.leaf (15)) (.leaf (17)))) (.branch 14 (.branch 13 (.leaf (1)) (.leaf (19))) (.branch 15 (.leaf (21)) (.leaf (22)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (23)) (.leaf (25))) (.branch 19 (.leaf (26)) (.leaf (28)))) (.branch 22 (.branch 21 (.leaf (4)) (.leaf (30))) (.branch 23 (.leaf (6)) (.leaf (32))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (33)) (.leaf (35))) (.branch 27 (.leaf (36)) (.leaf (37)))) (.branch 30 (.branch 29 (.leaf (20)) (.leaf (38))) (.branch 31 (.leaf (40)) (.leaf (10))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (16)) (.leaf (41))) (.branch 35 (.leaf (42)) (.leaf (12)))) (.branch 38 (.branch 37 (.leaf (39)) (.leaf (24))) (.branch 39 (.leaf (44)) (.leaf (45))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (47)) (.leaf (49))) (.branch 43 (.leaf (18)) (.leaf (34)))) (.branch 46 (.branch 45 (.leaf (50)) (.leaf (52))) (.branch 47 (.leaf (43)) (.leaf (48)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (31)) (.leaf (27))) (.branch 51 (.leaf (53)) (.leaf (29)))) (.branch 54 (.branch 53 (.leaf (55)) (.leaf (57))) (.branch 55 (.leaf (58)) (.leaf (56))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (46)) (.leaf (61))) (.branch 59 (.leaf (62)) (.leaf (63)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (51))) (.branch 63 (.leaf (54)) (.leaf (60))))))))
noncomputable def T (p : Fin 64) : Fin 64 :=
  tableLookup TData p.val
noncomputable def TiData : LookupTree (Fin 64) :=
  (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (5)) (.leaf (12))) (.branch 3 (.leaf (0)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (20)) (.leaf (2))) (.branch 7 (.leaf (22)) (.leaf (3))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (4)) (.leaf (6))) (.branch 11 (.leaf (31)) (.leaf (7)))) (.branch 14 (.branch 13 (.leaf (35)) (.leaf (8))) (.branch 15 (.leaf (9)) (.leaf (10)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (32)) (.leaf (11))) (.branch 19 (.leaf (42)) (.leaf (13)))) (.branch 22 (.branch 21 (.leaf (28)) (.leaf (14))) (.branch 23 (.leaf (15)) (.leaf (16))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (37)) (.leaf (17))) (.branch 27 (.leaf (18)) (.leaf (49)))) (.branch 30 (.branch 29 (.leaf (19)) (.leaf (51))) (.branch 31 (.leaf (21)) (.leaf (48))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (23)) (.leaf (24))) (.branch 35 (.leaf (43)) (.leaf (25)))) (.branch 38 (.branch 37 (.leaf (26)) (.leaf (27))) (.branch 39 (.leaf (29)) (.leaf (36))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (30)) (.leaf (33))) (.branch 43 (.leaf (34)) (.leaf (46)))) (.branch 46 (.branch 45 (.leaf (38)) (.leaf (39))) (.branch 47 (.leaf (56)) (.leaf (40)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (47)) (.leaf (41))) (.branch 51 (.leaf (44)) (.leaf (61)))) (.branch 54 (.branch 53 (.leaf (45)) (.leaf (50))) (.branch 55 (.leaf (62)) (.leaf (52))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (55)) (.leaf (53))) (.branch 59 (.leaf (54)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (63)) (.leaf (57))) (.branch 63 (.leaf (58)) (.leaf (59))))))))
noncomputable def Ti (p : Fin 64) : Fin 64 :=
  tableLookup TiData p.val
noncomputable def U (p : Fin 64) : Fin 64 := T (S p)
theorem quotient_relations : (∀ p : Fin 64, S (S p) = p ∧ U (U (U p)) = p ∧ Ti (T p) = p ∧ T (Ti p) = p) := by decide +kernel
theorem projection_compatible : ∀ p : Fin 128, projection (originalS p) = S (projection p) ∧ projection (originalT p) = T (projection p) := by decide +kernel
theorem central_quotient : (∀ p : Fin 128, projection (originalS (originalS p)) = projection p ∧ (representative (projection p) = p ∨ representative (projection p) = originalS (originalS p))) ∧ (∀ q : Fin 64, projection (representative q) = q) := by decide +kernel
noncomputable def vertices : List (List (Fin 64)) := [[0,3,9],[1,2,8],[4,5,14],[6,7,15],[10,11,23],[12,13,26],[16,17,33],[18,19,37],[20,21,38],[22],[24,25,42],[27,28,44],[29,30,45],[31,32,41],[34,35,36],[39,40,43],[46,47,53],[48,49,50],[51,52,58],[54,55,63],[56,57,59],[60,61,62]]
noncomputable def verticesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (4)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (6)) (.leaf (7))) (.branch 7 (.leaf (9)) (.leaf (10))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (5)) (.leaf (2))) (.branch 11 (.leaf (12)) (.leaf (13)))) (.branch 14 (.branch 13 (.leaf (15)) (.leaf (16))) (.branch 15 (.leaf (8)) (.leaf (11)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (18)) (.leaf (19))) (.branch 19 (.leaf (21)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (24)) (.leaf (25))) (.branch 23 (.leaf (27)) (.leaf (14))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (28)) (.leaf (29))) (.branch 27 (.leaf (17)) (.leaf (31)))) (.branch 30 (.branch 29 (.leaf (32)) (.leaf (34))) (.branch 31 (.leaf (35)) (.leaf (37))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (38)) (.leaf (20))) (.branch 35 (.leaf (40)) (.leaf (41)))) (.branch 38 (.branch 37 (.leaf (42)) (.leaf (23))) (.branch 39 (.leaf (26)) (.leaf (43))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (44)) (.leaf (39))) (.branch 43 (.leaf (30)) (.leaf (45)))) (.branch 46 (.branch 45 (.leaf (33)) (.leaf (36))) (.branch 47 (.leaf (46)) (.leaf (47)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (49)) (.leaf (50))) (.branch 51 (.leaf (51)) (.leaf (52)))) (.branch 54 (.branch 53 (.leaf (53)) (.leaf (48))) (.branch 55 (.leaf (55)) (.leaf (56))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (58)) (.leaf (59))) (.branch 59 (.leaf (54)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (61)) (.leaf (62))) (.branch 63 (.leaf (63)) (.leaf (57))))))))
noncomputable def verticesIndex (p : Fin 64) : Fin 64 := tableLookup verticesIndexData p.val
noncomputable def verticesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (9)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (2)) (.leaf (8))) (.branch 7 (.leaf (4)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (14)) (.leaf (6))) (.branch 11 (.leaf (7)) (.leaf (15)))) (.branch 14 (.branch 13 (.leaf (10)) (.leaf (11))) (.branch 15 (.leaf (23)) (.leaf (12)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (13)) (.leaf (26))) (.branch 19 (.leaf (16)) (.leaf (17)))) (.branch 22 (.branch 21 (.leaf (33)) (.leaf (18))) (.branch 23 (.leaf (19)) (.leaf (37))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (20)) (.leaf (21))) (.branch 27 (.leaf (38)) (.leaf (22)))) (.branch 30 (.branch 29 (.leaf (24)) (.leaf (25))) (.branch 31 (.leaf (42)) (.leaf (27))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (28)) (.leaf (44))) (.branch 35 (.leaf (29)) (.leaf (30)))) (.branch 38 (.branch 37 (.leaf (45)) (.leaf (31))) (.branch 39 (.leaf (32)) (.leaf (41))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (34)) (.leaf (35))) (.branch 43 (.leaf (36)) (.leaf (39)))) (.branch 46 (.branch 45 (.leaf (40)) (.leaf (43))) (.branch 47 (.leaf (46)) (.leaf (47)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (53)) (.leaf (48))) (.branch 51 (.leaf (49)) (.leaf (50)))) (.branch 54 (.branch 53 (.leaf (51)) (.leaf (52))) (.branch 55 (.leaf (58)) (.leaf (54))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (55)) (.leaf (63))) (.branch 59 (.leaf (56)) (.leaf (57)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (60))) (.branch 63 (.leaf (61)) (.leaf (62))))))))
noncomputable def verticesBack (p : Fin 64) : Fin 64 := tableLookup verticesBackData p.val
theorem vertices_index_inverse : ∀ p : Fin 64, verticesBack (verticesIndex p) = p := by decide +kernel
theorem vertices_enumeration : vertices.flatten.map verticesIndex = List.finRange 64 := by decide +kernel
theorem vertices_partition : ∀ p : Fin 64, (vertices.flatten.filter (· == p)).length = 1 :=
 partition_from_index vertices verticesIndex verticesBack vertices_index_inverse vertices_enumeration
theorem vertices_cycles : vertices.all (follows U) = true := by decide +kernel
noncomputable def edges : List (List (Fin 64)) := [[0,1],[2,4],[3,6],[5,9],[7,10],[8,12],[11,16],[13,18],[14,20],[15,22],[17,24],[19,27],[21,29],[23,31],[25,34],[26,35],[28,38],[30,39],[32,33],[36,43],[37,42],[40,46],[41,48],[44,49],[45,51],[47,50],[52,54],[53,56],[55,59],[57,60],[58,61],[62,63]]
noncomputable def edgesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (8))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (10)) (.leaf (7))) (.branch 11 (.leaf (9)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (14))) (.branch 15 (.leaf (16)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (13)) (.leaf (20))) (.branch 19 (.leaf (15)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (17)) (.leaf (24))) (.branch 23 (.leaf (19)) (.leaf (26))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (28))) (.branch 27 (.leaf (30)) (.leaf (23)))) (.branch 30 (.branch 29 (.leaf (32)) (.leaf (25))) (.branch 31 (.leaf (34)) (.leaf (27))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (36)) (.leaf (37))) (.branch 35 (.leaf (29)) (.leaf (31)))) (.branch 38 (.branch 37 (.leaf (38)) (.leaf (40))) (.branch 39 (.leaf (33)) (.leaf (35))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (42)) (.leaf (44))) (.branch 43 (.leaf (41)) (.leaf (39)))) (.branch 46 (.branch 45 (.leaf (46)) (.leaf (48))) (.branch 47 (.leaf (43)) (.leaf (50)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (45)) (.leaf (47))) (.branch 51 (.leaf (51)) (.leaf (49)))) (.branch 54 (.branch 53 (.leaf (52)) (.leaf (54))) (.branch 55 (.leaf (53)) (.leaf (56))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (55)) (.leaf (58))) (.branch 59 (.leaf (60)) (.leaf (57)))) (.branch 62 (.branch 61 (.leaf (59)) (.leaf (61))) (.branch 63 (.leaf (62)) (.leaf (63))))))))
noncomputable def edgesIndex (p : Fin 64) : Fin 64 := tableLookup edgesIndexData p.val
noncomputable def edgesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (1))) (.branch 3 (.leaf (2)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (6))) (.branch 7 (.leaf (5)) (.leaf (9))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (7)) (.leaf (10))) (.branch 11 (.leaf (8)) (.leaf (12)))) (.branch 14 (.branch 13 (.leaf (11)) (.leaf (16))) (.branch 15 (.leaf (13)) (.leaf (18)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (14)) (.leaf (20))) (.branch 19 (.leaf (15)) (.leaf (22)))) (.branch 22 (.branch 21 (.leaf (17)) (.leaf (24))) (.branch 23 (.leaf (19)) (.leaf (27))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (21)) (.leaf (29))) (.branch 27 (.leaf (23)) (.leaf (31)))) (.branch 30 (.branch 29 (.leaf (25)) (.leaf (34))) (.branch 31 (.leaf (26)) (.leaf (35))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (28)) (.leaf (38))) (.branch 35 (.leaf (30)) (.leaf (39)))) (.branch 38 (.branch 37 (.leaf (32)) (.leaf (33))) (.branch 39 (.leaf (36)) (.leaf (43))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (37)) (.leaf (42))) (.branch 43 (.leaf (40)) (.leaf (46)))) (.branch 46 (.branch 45 (.leaf (41)) (.leaf (48))) (.branch 47 (.leaf (44)) (.leaf (49)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (45)) (.leaf (51))) (.branch 51 (.leaf (47)) (.leaf (50)))) (.branch 54 (.branch 53 (.leaf (52)) (.leaf (54))) (.branch 55 (.leaf (53)) (.leaf (56))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (55)) (.leaf (59))) (.branch 59 (.leaf (57)) (.leaf (60)))) (.branch 62 (.branch 61 (.leaf (58)) (.leaf (61))) (.branch 63 (.leaf (62)) (.leaf (63))))))))
noncomputable def edgesBack (p : Fin 64) : Fin 64 := tableLookup edgesBackData p.val
theorem edges_index_inverse : ∀ p : Fin 64, edgesBack (edgesIndex p) = p := by decide +kernel
theorem edges_enumeration : edges.flatten.map edgesIndex = List.finRange 64 := by decide +kernel
theorem edges_partition : ∀ p : Fin 64, (edges.flatten.filter (· == p)).length = 1 :=
 partition_from_index edges edgesIndex edgesBack edges_index_inverse edges_enumeration
theorem edges_cycles : edges.all (follows S) = true := by decide +kernel
noncomputable def faces : List (List (Fin 64)) := [[0,2,5],[1,3,7,11,17,25,35,12],[4,8,13,19,28,20],[6,9,14,21,30,40,47,48,31,10,15,22],[16,23,32],[18,26,36,39,45,52,55,56,46,43,34,42],[24,33,41,49,27,37],[29,38,44,50,53,57,61,51],[54,58,62],[59,63,60]]
noncomputable def facesIndexData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (3))) (.branch 3 (.leaf (1)) (.leaf (4)))) (.branch 6 (.branch 5 (.leaf (11)) (.leaf (2))) (.branch 7 (.leaf (17)) (.leaf (5))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (12)) (.leaf (18))) (.branch 11 (.leaf (26)) (.leaf (6)))) (.branch 14 (.branch 13 (.leaf (10)) (.leaf (13))) (.branch 15 (.leaf (19)) (.leaf (27)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (29)) (.leaf (7))) (.branch 19 (.leaf (32)) (.leaf (14)))) (.branch 22 (.branch 21 (.leaf (16)) (.leaf (20))) (.branch 23 (.leaf (28)) (.leaf (30))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (44)) (.leaf (8))) (.branch 27 (.leaf (33)) (.leaf (48)))) (.branch 30 (.branch 29 (.leaf (15)) (.leaf (50))) (.branch 31 (.leaf (21)) (.leaf (25))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (31)) (.leaf (45))) (.branch 35 (.leaf (42)) (.leaf (9)))) (.branch 38 (.branch 37 (.leaf (34)) (.leaf (49))) (.branch 39 (.leaf (51)) (.leaf (35))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (22)) (.leaf (46))) (.branch 43 (.leaf (43)) (.leaf (41)))) (.branch 46 (.branch 45 (.leaf (52)) (.leaf (36))) (.branch 47 (.leaf (40)) (.leaf (23)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (24)) (.leaf (47))) (.branch 51 (.leaf (53)) (.leaf (57)))) (.branch 54 (.branch 53 (.leaf (37)) (.leaf (54))) (.branch 55 (.leaf (58)) (.leaf (38))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (39)) (.leaf (55))) (.branch 59 (.leaf (59)) (.leaf (61)))) (.branch 62 (.branch 61 (.leaf (63)) (.leaf (56))) (.branch 63 (.leaf (60)) (.leaf (62))))))))
noncomputable def facesIndex (p : Fin 64) : Fin 64 := tableLookup facesIndexData p.val
noncomputable def facesBackData : LookupTree (Fin 64) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (0)) (.leaf (2))) (.branch 3 (.leaf (5)) (.leaf (1)))) (.branch 6 (.branch 5 (.leaf (3)) (.leaf (7))) (.branch 7 (.leaf (11)) (.leaf (17))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (25)) (.leaf (35))) (.branch 11 (.leaf (12)) (.leaf (4)))) (.branch 14 (.branch 13 (.leaf (8)) (.leaf (13))) (.branch 15 (.leaf (19)) (.leaf (28)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (20)) (.leaf (6))) (.branch 19 (.leaf (9)) (.leaf (14)))) (.branch 22 (.branch 21 (.leaf (21)) (.leaf (30))) (.branch 23 (.leaf (40)) (.leaf (47))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (48)) (.leaf (31))) (.branch 27 (.leaf (10)) (.leaf (15)))) (.branch 30 (.branch 29 (.leaf (22)) (.leaf (16))) (.branch 31 (.leaf (23)) (.leaf (32))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (18)) (.leaf (26))) (.branch 35 (.leaf (36)) (.leaf (39)))) (.branch 38 (.branch 37 (.leaf (45)) (.leaf (52))) (.branch 39 (.leaf (55)) (.leaf (56))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (46)) (.leaf (43))) (.branch 43 (.leaf (34)) (.leaf (42)))) (.branch 46 (.branch 45 (.leaf (24)) (.leaf (33))) (.branch 47 (.leaf (41)) (.leaf (49)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (27)) (.leaf (37))) (.branch 51 (.leaf (29)) (.leaf (38)))) (.branch 54 (.branch 53 (.leaf (44)) (.leaf (50))) (.branch 55 (.leaf (53)) (.leaf (57))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (61)) (.leaf (51))) (.branch 59 (.leaf (54)) (.leaf (58)))) (.branch 62 (.branch 61 (.leaf (62)) (.leaf (59))) (.branch 63 (.leaf (63)) (.leaf (60))))))))
noncomputable def facesBack (p : Fin 64) : Fin 64 := tableLookup facesBackData p.val
theorem faces_index_inverse : ∀ p : Fin 64, facesBack (facesIndex p) = p := by decide +kernel
theorem faces_enumeration : faces.flatten.map facesIndex = List.finRange 64 := by decide +kernel
theorem faces_partition : ∀ p : Fin 64, (faces.flatten.filter (· == p)).length = 1 :=
 partition_from_index faces facesIndex facesBack faces_index_inverse faces_enumeration
theorem faces_cycles : faces.all (follows T) = true := by decide +kernel
theorem vertex_valencies : vertices.all (fun v => v.length == 1 || v.length == 3) = true := by decide +kernel
theorem edge_valencies : edges.all (fun e => e.length == 1 || e.length == 2) = true := by decide +kernel
theorem cusp_widths : faces.map List.length = [3,8,6,12,3,12,6,8,3,3] := by decide +kernel
theorem euler_arithmetic : (2 - 2 * 1 : Int) = 22 - 32 + 10 + 0 := by decide +kernel
theorem elliptic_counts : (edges.filter (fun e => e.length == 1)).length = 0 ∧ (vertices.filter (fun v => v.length == 1)).length = 1 := by decide +kernel
noncomputable def liftMatrixData : LookupTree (Mat) :=
 (.branch 32 (.branch 16 (.branch 8 (.branch 4 (.branch 2 (.branch 1 (.leaf (⟨1,0,0,1⟩)) (.leaf (⟨0,-1,1,0⟩))) (.branch 3 (.leaf (⟨-1,-1,0,-1⟩)) (.leaf (⟨0,-1,1,1⟩)))) (.branch 6 (.branch 5 (.leaf (⟨-1,1,-1,0⟩)) (.leaf (⟨1,2,0,1⟩))) (.branch 7 (.leaf (⟨-1,0,1,-1⟩)) (.leaf (⟨0,1,-1,-2⟩))))) (.branch 12 (.branch 10 (.branch 9 (.leaf (⟨-1,0,-1,-1⟩)) (.leaf (⟨-1,-1,1,0⟩))) (.branch 11 (.leaf (⟨1,0,-2,1⟩)) (.leaf (⟨0,-1,1,3⟩)))) (.branch 14 (.branch 13 (.leaf (⟨0,1,-1,1⟩)) (.leaf (⟨1,1,1,2⟩))) (.branch 15 (.leaf (⟨2,1,1,1⟩)) (.leaf (⟨1,1,-2,-1⟩)))))) (.branch 24 (.branch 20 (.branch 18 (.branch 17 (.leaf (⟨-1,0,3,-1⟩)) (.leaf (⟨0,1,-1,-4⟩))) (.branch 19 (.leaf (⟨1,-1,2,-1⟩)) (.leaf (⟨-1,-2,-1,-3⟩)))) (.branch 22 (.branch 21 (.leaf (⟨1,-2,1,-1⟩)) (.leaf (⟨-2,-3,-1,-2⟩))) (.branch 23 (.leaf (⟨1,-1,-1,2⟩)) (.leaf (⟨-1,-1,3,2⟩))))) (.branch 28 (.branch 26 (.branch 25 (.leaf (⟨2,3,3,5⟩)) (.leaf (⟨3,1,5,2⟩))) (.branch 27 (.leaf (⟨1,0,2,1⟩)) (.leaf (⟨4,1,3,1⟩)))) (.branch 30 (.branch 29 (.leaf (⟨-1,3,-1,2⟩)) (.leaf (⟨-3,2,-2,1⟩))) (.branch 31 (.leaf (⟨2,5,1,3⟩)) (.leaf (⟨-1,1,2,-3⟩))))))) (.branch 48 (.branch 40 (.branch 36 (.branch 34 (.branch 33 (.leaf (⟨1,2,-3,-5⟩)) (.leaf (⟨1,1,-4,-3⟩))) (.branch 35 (.leaf (⟨-1,0,-3,-1⟩)) (.leaf (⟨0,-1,1,-2⟩)))) (.branch 38 (.branch 37 (.leaf (⟨-1,-1,-2,-3⟩)) (.leaf (⟨-2,-1,-3,-2⟩))) (.branch 39 (.leaf (⟨-3,-1,-2,-1⟩)) (.leaf (⟨1,2,2,5⟩))))) (.branch 44 (.branch 42 (.branch 41 (.leaf (⟨2,1,5,3⟩)) (.leaf (⟨2,1,-5,-2⟩))) (.branch 43 (.leaf (⟨-1,2,-2,3⟩)) (.leaf (⟨-1,1,-3,2⟩)))) (.branch 46 (.branch 45 (.leaf (⟨3,4,2,3⟩)) (.leaf (⟨5,3,3,2⟩))) (.branch 47 (.leaf (⟨1,-2,3,-5⟩)) (.leaf (⟨-2,-3,-5,-8⟩)))))) (.branch 56 (.branch 52 (.branch 50 (.branch 49 (.leaf (⟨-7,-4,-5,-3⟩)) (.leaf (⟨4,-3,3,-2⟩))) (.branch 51 (.leaf (⟨-3,-7,-2,-5⟩)) (.leaf (⟨3,-5,2,-3⟩)))) (.branch 54 (.branch 53 (.leaf (⟨-5,-8,-3,-5⟩)) (.leaf (⟨-3,-1,-8,-3⟩))) (.branch 55 (.leaf (⟨-8,5,-5,3⟩)) (.leaf (⟨5,13,3,8⟩))))) (.branch 60 (.branch 58 (.branch 57 (.leaf (⟨-1,3,-3,8⟩)) (.leaf (⟨3,4,8,11⟩))) (.branch 59 (.leaf (⟨-8,-3,-5,-2⟩)) (.leaf (⟨4,1,11,3⟩)))) (.branch 62 (.branch 61 (.leaf (⟨11,3,7,2⟩)) (.leaf (⟨-3,8,-2,5⟩))) (.branch 63 (.leaf (⟨8,11,5,7⟩)) (.leaf (⟨13,8,8,5⟩))))))))
noncomputable def liftMatrix (p : Fin 64) : Mat := tableLookup liftMatrixData p.val
noncomputable def lifts : List (Witness 64) := [⟨⟨1,0,0,1⟩,[.t (0)],0⟩,⟨⟨0,-1,1,0⟩,[.t (0),.s,.t (0)],1⟩,⟨⟨-1,-1,0,-1⟩,[.t (1)],2⟩,⟨⟨0,-1,1,1⟩,[.t (0),.s,.t (1)],3⟩,⟨⟨-1,1,-1,0⟩,[.t (1),.s,.t (0)],4⟩,⟨⟨1,2,0,1⟩,[.t (2)],5⟩,⟨⟨-1,0,1,-1⟩,[.t (-1),.s,.t (-1)],6⟩,⟨⟨0,1,-1,-2⟩,[.t (0),.s,.t (2)],7⟩,⟨⟨-1,0,-1,-1⟩,[.t (1),.s,.t (1)],8⟩,⟨⟨-1,-1,1,0⟩,[.t (-1),.s,.t (0)],9⟩,⟨⟨1,0,-2,1⟩,[.t (-1),.s,.t (-2),.s,.t (-1)],10⟩,⟨⟨0,-1,1,3⟩,[.t (0),.s,.t (3)],11⟩,⟨⟨0,1,-1,1⟩,[.t (0),.s,.t (-1)],12⟩,⟨⟨1,1,1,2⟩,[.t (1),.s,.t (2)],13⟩,⟨⟨2,1,1,1⟩,[.t (2),.s,.t (1)],14⟩,⟨⟨1,1,-2,-1⟩,[.t (-1),.s,.t (-2),.s,.t (0)],15⟩,⟨⟨-1,0,3,-1⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-1)],16⟩,⟨⟨0,1,-1,-4⟩,[.t (0),.s,.t (4)],17⟩,⟨⟨1,-1,2,-1⟩,[.t (0),.s,.t (-2),.s,.t (-1)],18⟩,⟨⟨-1,-2,-1,-3⟩,[.t (1),.s,.t (3)],19⟩,⟨⟨1,-2,1,-1⟩,[.t (1),.s,.t (-1)],20⟩,⟨⟨-2,-3,-1,-2⟩,[.t (2),.s,.t (2)],21⟩,⟨⟨1,-1,-1,2⟩,[.t (-1),.s,.t (-2)],22⟩,⟨⟨-1,-1,3,2⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (0)],23⟩,⟨⟨2,3,3,5⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (1)],24⟩,⟨⟨3,1,5,2⟩,[.t (0),.s,.t (-2),.s,.t (-3),.s,.t (0)],25⟩,⟨⟨1,0,2,1⟩,[.t (0),.s,.t (-2),.s,.t (0)],26⟩,⟨⟨4,1,3,1⟩,[.t (1),.s,.t (-3),.s,.t (0)],27⟩,⟨⟨-1,3,-1,2⟩,[.t (1),.s,.t (-2)],28⟩,⟨⟨-3,2,-2,1⟩,[.t (1),.s,.t (-2),.s,.t (-1)],29⟩,⟨⟨2,5,1,3⟩,[.t (2),.s,.t (3)],30⟩,⟨⟨-1,1,2,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2)],31⟩,⟨⟨1,2,-3,-5⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (1)],32⟩,⟨⟨1,1,-4,-3⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (0)],33⟩,⟨⟨-1,0,-3,-1⟩,[.t (0),.s,.t (-3),.s,.t (0)],34⟩,⟨⟨0,-1,1,-2⟩,[.t (0),.s,.t (-2)],35⟩,⟨⟨-1,-1,-2,-3⟩,[.t (0),.s,.t (-2),.s,.t (1)],36⟩,⟨⟨-2,-1,-3,-2⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (0)],37⟩,⟨⟨-3,-1,-2,-1⟩,[.t (1),.s,.t (-2),.s,.t (0)],38⟩,⟨⟨1,2,2,5⟩,[.t (0),.s,.t (-2),.s,.t (2)],39⟩,⟨⟨2,1,5,3⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (0)],40⟩,⟨⟨2,1,-5,-2⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (0)],41⟩,⟨⟨-1,2,-2,3⟩,[.t (0),.s,.t (-2),.s,.t (-2)],42⟩,⟨⟨-1,1,-3,2⟩,[.t (0),.s,.t (-3),.s,.t (-1)],43⟩,⟨⟨3,4,2,3⟩,[.t (1),.s,.t (-2),.s,.t (1)],44⟩,⟨⟨5,3,3,2⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (0)],45⟩,⟨⟨1,-2,3,-5⟩,[.t (0),.s,.t (-3),.s,.t (-2)],46⟩,⟨⟨-2,-3,-5,-8⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (1)],47⟩,⟨⟨-7,-4,-5,-3⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (0)],48⟩,⟨⟨4,-3,3,-2⟩,[.t (1),.s,.t (-3),.s,.t (-1)],49⟩,⟨⟨-3,-7,-2,-5⟩,[.t (1),.s,.t (-2),.s,.t (2)],50⟩,⟨⟨3,-5,2,-3⟩,[.t (1),.s,.t (-2),.s,.t (-2)],51⟩,⟨⟨-5,-8,-3,-5⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (1)],52⟩,⟨⟨-3,-1,-8,-3⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (0)],53⟩,⟨⟨-8,5,-5,3⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-1)],54⟩,⟨⟨5,13,3,8⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (2)],55⟩,⟨⟨-1,3,-3,8⟩,[.t (0),.s,.t (-3),.s,.t (-3)],56⟩,⟨⟨3,4,8,11⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (1)],57⟩,⟨⟨-8,-3,-5,-2⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (0)],58⟩,⟨⟨4,1,11,3⟩,[.t (0),.s,.t (-3),.s,.t (-4),.s,.t (0)],59⟩,⟨⟨11,3,7,2⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (0)],60⟩,⟨⟨-3,8,-2,5⟩,[.t (1),.s,.t (-2),.s,.t (-3)],61⟩,⟨⟨8,11,5,7⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (1)],62⟩,⟨⟨13,8,8,5⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (0)],63⟩]
theorem lift_words : ∀ w ∈ lifts, WitnessValid S T Ti 0 w :=
 all_of_check lifts (WitnessValid S T Ti 0) (by decide +kernel)
theorem lift_matrices_match : lifts.length = 64 ∧ ((List.finRange 64).zip lifts).all (fun pw => pw.2.matrix == liftMatrix pw.1 && pw.2.point == pw.1) = true := by decide +kernel
noncomputable def sides : List (Side 64) := [⟨9,1,⟨⟨-1,-3,0,-1⟩,[.t (3)],0⟩⟩,⟨22,-3,⟨⟨-4,-3,7,5⟩,[.t (-1),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (0)],0⟩⟩,⟨41,7,⟨⟨43,18,31,13⟩,[.t (1),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨32,6,⟨⟨-8,-3,27,10⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (0)],0⟩⟩,⟨33,6,⟨⟨10,3,-27,-8⟩,[.t (-1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (0)],0⟩⟩,⟨17,2,⟨⟨-14,-3,-23,-5⟩,[.t (0),.s,.t (-2),.s,.t (-3),.s,.t (-5),.s,.t (0)],0⟩⟩,⟨34,4,⟨⟨10,-3,17,-5⟩,[.t (0),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨59,9,⟨⟨-94,33,-57,20⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨57,10,⟨⟨121,-45,78,-29⟩,[.t (1),.s,.t (-2),.s,.t (-6),.s,.t (-2),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨47,8,⟨⟨71,-27,50,-19⟩,[.t (1),.s,.t (-3),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨39,5,⟨⟨-29,12,-17,7⟩,[.t (1),.s,.t (-2),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-1)],0⟩⟩,⟨25,4,⟨⟨-5,3,-17,10⟩,[.t (0),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨24,2,⟨⟨-5,3,23,-14⟩,[.t (-1),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-1)],0⟩⟩,⟨19,3,⟨⟨-7,6,-6,5⟩,[.t (1),.s,.t (-6),.s,.t (-1)],0⟩⟩,⟨27,3,⟨⟨5,-6,6,-7⟩,[.t (0),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨48,7,⟨⟨13,-18,-31,43⟩,[.t (-1),.s,.t (-2),.s,.t (-4),.s,.t (-3),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨50,8,⟨⟨-19,27,-50,71⟩,[.t (0),.s,.t (-3),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-2)],0⟩⟩,⟨60,10,⟨⟨-29,45,-78,121⟩,[.t (0),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-2),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨62,11,⟨⟨121,-192,75,-119⟩,[.t (1),.s,.t (-2),.s,.t (-3),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨63,11,⟨⟨-119,192,-75,121⟩,[.t (1),.s,.t (-2),.s,.t (-4),.s,.t (-2),.s,.t (-3),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨55,9,⟨⟨20,-33,57,-94⟩,[.t (0),.s,.t (-3),.s,.t (-7),.s,.t (-3),.s,.t (-2)],0⟩⟩,⟨30,5,⟨⟨7,-12,17,-29⟩,[.t (0),.s,.t (-3),.s,.t (-2),.s,.t (-4),.s,.t (-2)],0⟩⟩,⟨5,1,⟨⟨-1,3,0,-1⟩,[.t (-3)],0⟩⟩]
theorem side_pairing_words : ∀ sd ∈ sides, SideValid S T Ti 0 liftMatrix sd :=
 all_of_check sides (SideValid S T Ti 0 liftMatrix) (by decide +kernel)
noncomputable def boundary : List (Int × Int) := [(1,0),(-1,1),(-1,2),(-2,5),(-1,3),(-1,4),(0,1),(1,3),(4,11),(3,8),(2,5),(1,2),(3,5),(2,3),(1,1),(4,3),(7,5),(3,2),(11,7),(8,5),(13,8),(5,3),(2,1),(1,0)]
theorem boundary_farey_neighbors : ∀ pq ∈ adjacent boundary, FareyNeighbor pq :=
 all_of_check (adjacent boundary) FareyNeighbor (by decide +kernel)
theorem boundary_matches_darts : (adjacent boundary).length = sides.length ∧ ((adjacent boundary).zip sides).all (fun item => matchesEdge item.1 (liftMatrix item.2.dart)) = true := by decide +kernel
theorem boundary_order : (adjacent (boundary.drop 1 |>.take (boundary.length - 2))).all (fun pq => pq.1.2 > 0 && pq.2.2 > 0 && pq.1.1*pq.2.2 < pq.2.1*pq.1.2) = true := by decide +kernel
noncomputable def freeLabels : List Int := [1,2,3,4,5,6,7,8,9,10,11]
theorem paired_sides : freeLabels.all (fun k => let ss := sides.filter (fun sd => sd.label == k); ss.length == 2 && decide (samePSL (ss.getD 0 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix (inv (ss.getD 1 ⟨0,0,⟨⟨1,0,0,1⟩,[],0⟩⟩).witness.matrix))) = true := by decide +kernel
end G192_4_c3

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
