import Mathlib.Data.Fin.Basic

/- A closed lookup tree avoids substituting the input throughout a large
   function body on each kernel reduction. Included in the largest certificate. -/
namespace ChenMore

inductive LookupTree (α : Type) where
  | leaf : α → LookupTree α
  | branch : Nat → LookupTree α → LookupTree α → LookupTree α

def tableLookup {α : Type} (tree : LookupTree α) (p : Nat) : α :=
  match tree with
  | .leaf value => value
  | .branch cut left right =>
      if p < cut then tableLookup left p else tableLookup right p

#print axioms tableLookup
end ChenMore
