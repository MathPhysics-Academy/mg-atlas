import Mathlib.Data.Fin.Basic
import Lean.Util.CollectAxioms

/- A certificate for the nine-point action computed for Chen's S₄ row.
   Finite checks use kernel reduction (`decide`), with no native_decide,
   sorry, or additional axioms. Standard Lean axioms are reported below.
   Identification with generating pairs of S₄ is NOT asserted here. -/
namespace ChenS4

abbrev Point := Fin 9

def S (p : Point) : Point :=
  (#[1, 0, 4, 5, 2, 3, 6, 8, 7] : Array Point)[p.val]'(by simp)
def T (p : Point) : Point :=
  (#[2, 3, 0, 6, 7, 4, 8, 5, 1] : Array Point)[p.val]'(by simp)

inductive Letter where
  | s | t
  deriving DecidableEq, Repr
open Letter
abbrev Word := List Letter

def act (p : Point) (w : Word) : Point :=
  w.foldl (fun q a => match a with | s => S q | t => T q) p

-- In particular S and T are permutations; these are the PSL₂ presentation relations.
theorem S_squared : ∀ p, S (S p) = p := by decide
theorem ST_cubed : ∀ p, act p [s,t,s,t,s,t] = p := by decide
theorem T_bijective : (∀ p q, T p = T q → p = q) ∧
    (∀ q, ∃ p, T p = q) := by decide

def orbitWords : List Word :=
  [[], [s], [t], [s,t], [t,s], [s,t,s], [s,t,t], [t,s,t], [s,t,t,t]]

-- Explicit paths from point 0 cover all nine points, hence there is one component.
theorem transitive_certificate :
    ∀ p : Point, p ∈ orbitWords.map (act 0) := by decide

def points : List Point := List.finRange 9

theorem elliptic_counts :
    (points.filter (fun p => S p == p)).length = 1 ∧
    (points.filter (fun p => T (S p) == p)).length = 0 := by decide

-- The three cusp cycles have lengths 2, 4, 3 (sorted widths: 2, 3, 4).
def cuspCycles : List (List Point) := [[0,2], [1,3,6,8], [4,7,5]]

def followsT (c : List Point) : Bool :=
  !c.isEmpty && (c.zip (c.drop 1 ++ c.take 1)).all (fun pq => T pq.1 == pq.2)

theorem cusp_certificate :
    cuspCycles.all followsT = true ∧
    (∀ p : Point, (cuspCycles.flatten.filter (· == p)).length = 1) ∧
    cuspCycles.map List.length = [2,4,3] := by decide

-- Arithmetic in the modular-curve genus formula, not a formal geometric theorem.
theorem genus_arithmetic :
    (12 * 0 : Int) = 12 + 9 - 3 * 1 - 4 * 0 - 6 * 3 := by decide
theorem cusp_lcm : Nat.lcm 2 (Nat.lcm 3 4) = 12 := by decide

structure Matrix12 where
  a : Fin 12
  b : Fin 12
  c : Fin 12
  d : Fin 12
  deriving DecidableEq, Repr

def matrixStep (m : Matrix12) : Letter → Matrix12
  | s => ⟨m.b, ⟨(12 - m.a.val) % 12, Nat.mod_lt _ (by decide)⟩,
           m.d, ⟨(12 - m.c.val) % 12, Nat.mod_lt _ (by decide)⟩⟩
  | t => ⟨m.a, ⟨(m.a.val + m.b.val) % 12, Nat.mod_lt _ (by decide)⟩,
           m.c, ⟨(m.c.val + m.d.val) % 12, Nat.mod_lt _ (by decide)⟩⟩

-- Right multiplication by the standard S and T matrices, reduced modulo 12.
def matrixOf (w : Word) : Matrix12 := w.foldl matrixStep ⟨1,0,0,1⟩

def wordA : Word := [s,t,t,t,t,s,t,t,t]
def wordB : Word := [t,t,t,s,t,t,t,t,s]

theorem same_matrix : matrixOf wordA = matrixOf wordB := by decide
theorem different_points : act 0 wordA ≠ act 0 wordB := by decide

-- A factorization would assign the same point to these equal residue matrices.
-- This certifies failure at modulus 12. The level theorem needed to deduce
-- noncongruence of a modular subgroup is outside this prototype.
theorem no_factor_mod12 :
    ¬ ∃ f : Matrix12 → Point, ∀ w : Word, f (matrixOf w) = act 0 w := by
  rintro ⟨f, hf⟩
  have h := congrArg f same_matrix
  rw [hf wordA, hf wordB] at h
  exact different_points h

#print axioms S_squared
#print axioms ST_cubed
#print axioms T_bijective
#print axioms transitive_certificate
#print axioms elliptic_counts
#print axioms cusp_certificate
#print axioms genus_arithmetic
#print axioms cusp_lcm
#print axioms same_matrix
#print axioms different_points
#print axioms no_factor_mod12

-- Fail compilation if ANY declaration in this namespace depends on an axiom
-- outside Lean's three standard logical axioms (including sorryAx).
run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "ChenS4." then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Axiom audit failed: {name} depends on {ax}"
      count := count + 1
  Lean.logInfo m!"Axiom audit passed for all {count} ChenS4 declarations; allowed: {allowed}"

end ChenS4
