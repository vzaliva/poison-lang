import Std.Data.HashMap
open Std

/--
  Generic map-combine for HashMap. Produces a new map by applying `f` to each key
  in the union of domains. The function `f` receives the key and the optional
  values from the left and right maps and returns the resulting optional value.
  If `f` returns `none`, the key is omitted from the result.
-/
def combineMaps [BEq α] [Hashable α]
  (m1 : HashMap α β) (m2 : HashMap α β)
  (f : α → Option β → Option β → Option β) : HashMap α β :=
  let afterLeft := m1.fold (init := ({} : HashMap α β)) fun acc k v =>
    match f k (some v) (m2.get? k) with
    | some r => acc.insert k r
    | none   => acc.erase k
  -- Process keys that appear only in the right map
  m2.fold (init := afterLeft) fun acc k v =>
    if m1.contains k then acc
    else
      match f k none (some v) with
      | some r => acc.insert k r
      | none   => acc.erase k


