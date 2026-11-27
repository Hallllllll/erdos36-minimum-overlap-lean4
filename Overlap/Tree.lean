import Init

namespace Overlap

/-- The left subtree stores the less significant digits. -/
inductive Tree where
  | leaf (value : Nat)
  | node (left right : Tree)

namespace Tree

def size : Tree → Nat
  | .leaf _ => 1
  | .node l r => l.size + r.size

def total : Tree → Nat
  | .leaf x => x
  | .node l r => l.total + r.total

def high : Tree → Nat
  | .leaf x => x
  | .node l r => max l.high r.high

def pack (b : Nat) : Tree → Nat
  | .leaf x => x
  | .node l r => pack b l + b ^ l.size * pack b r

/-- Encode the reversed list of complements, in the same base. -/
def other (b d : Nat) : Tree → Nat
  | .leaf x => d - x
  | .node l r => other b d r + b ^ r.size * other b d l

def items : Tree → List Nat
  | .leaf x => [x]
  | .node l r => l.items ++ r.items

end Tree
end Overlap
