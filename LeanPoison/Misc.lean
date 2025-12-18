import Init.Data.List
import Std.Data.HashMap
import Std.Data.ExtTreeMap
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


/--
  Generic map-combine for ExtTreeMap. Produces a new map by applying `f` to each key
  in the union of domains. The function `f` receives the key and the optional
  values from the left and right maps and returns the resulting optional value.
  If `f` returns `none`, the key is omitted from the result.
-/
def combineExtTreeMaps [Ord α] [BEq α] [TransCmp (compare : α → α → Ordering)]
  (m₁ m₂ : ExtTreeMap α β)
  (f : α → Option β → Option β → Option β)
  : ExtTreeMap α β :=
  -- Collect all keys from both maps using fold
  let keys1 := m₁.foldl (init := []) fun acc k _ => k :: acc
  let keys2 := m₂.foldl (init := []) fun acc k _ => k :: acc
  let ks := (keys1 ++ keys2).eraseDups
  let rec go : List α → ExtTreeMap α β → ExtTreeMap α β
  | [],     acc => acc
  | k::ks,  acc =>
      let acc' :=
        match f k (m₁.get? k) (m₂.get? k) with
        | some v => acc.insert k v
        | none   => acc.erase k
      go ks acc'
  go ks ({} : ExtTreeMap α β)

/-- Concatenate lists while removing duplicates -/
def concat_noDups [BEq α] (l₁ l₂ : List α) : List α :=
  let l := l₁ ++ l₂
  l.eraseDups
