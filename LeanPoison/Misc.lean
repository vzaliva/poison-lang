import Init.Data.List
import Std.Data.HashMap
import Mathlib.Data.List.Lattice


open Std


/--
  Generic map-combine for HashMap. Produces a new map by applying `f` to each key
  in the union of domains. The function `f` receives the key and the optional
  values from the left and right maps and returns the resulting optional value.
  If `f` returns `none`, the key is omitted from the result.
-/
def combineMaps [BEq α] [Hashable α] [DecidableEq α]
  (m₁ m₂ : HashMap α β)
  (f : α → Option β → Option β → Option β)
  : HashMap α β :=
  let ks := (m₁.keys ++ m₂.keys).dedup
  let rec go : List α → HashMap α β → HashMap α β
  | [],     acc => acc
  | k::ks,  acc =>
      let acc' :=
        match f k (m₁.get? k) (m₂.get? k) with
        | some v => acc.insert k v
        | none   => acc.erase k
      go ks acc'
  go ks ({} : HashMap α β)

/-
Structural equality for HashMap
-/
instance [BEq α] [Hashable α] [BEq β] : BEq (HashMap α β) where
  beq m₁ m₂ :=
    if m₁.size != m₂.size then
      false
    else
      m₁.fold (init := true) fun acc k v =>
        acc && match m₂.get? k with
          | some v' => v == v'
          | none    => false


/-- Concatenate lists while removing duplicates -/
def concat_noDups [BEq α] (l₁ l₂ : List α) : List α :=
  let l := l₁ ++ l₂
  l.eraseDups
