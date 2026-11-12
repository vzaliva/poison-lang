import LeanPoison.Syntax
import LeanPoison.Typecheck
import LeanProofs.Auxiliary
import LeanProofs.TypeSafety
import LeanProofs.RegimeConsistency
import Std.Data.ExtTreeMap
import Std.Data.ExtTreeMap.Lemmas

-- Program tables of typing runs.  A typing run records the guards it
-- allocates (`TypeResult.tagLog'`).  This module relates those logs to tag
-- meanings:
--
-- * `LogFresh`: the allocations of a run carry tags in a range, and two
--   allocations with the same tag are the same allocation
--   (`typecheck_tagLog_fresh` proves it for every successful run);
-- * `programTable tm log`: the table `tm` with every allocation of `log`;
-- * `WithinLog`: a table that adds to another only allocations of a log;
-- * `TagFrame`: a lawful table that contains the current table and every
--   allocation of the current run.  The step theorems thread it alongside the
--   law at the current table.

open Std

/-- The guard descriptor an allocation records. -/
def TagAlloc.desc (a : TagAlloc) : GuardDesc :=
  { argName := a.argName, body := a.body, capEnv := a.capEnv }

/-- Every allocation of `log` is recorded in the table `P`. -/
def LogIn (log : List TagAlloc) (P : TagMeaning) : Prop :=
  ∀ a ∈ log, P.lookup a.tag = some a.desc

/-- `tm'` adds to `tm` only allocations of `log`. -/
def WithinLog (tm : TagMeaning) (log : List TagAlloc) (tm' : TagMeaning) : Prop :=
  ∀ t d, tm'.lookup t = some d → tm.lookup t = some d ∨ ∃ a ∈ log, a.tag = t ∧ a.desc = d

/-- The tags of `log` lie in `[lo, hi)`, and two allocations with the same tag
    are the same allocation. -/
def LogFresh (lo hi : Tag) (log : List TagAlloc) : Prop :=
  (∀ a ∈ log, lo ≤ a.tag ∧ a.tag < hi) ∧
  (∀ a ∈ log, ∀ b ∈ log, a.tag = b.tag → a = b)

/-- The table `tm` with every allocation of `log`. -/
def programTable (tm : TagMeaning) (log : List TagAlloc) : TagMeaning :=
  log.foldl (fun acc a => acc.update a.tag a.desc) tm

/-- A lawful table `P` that contains the current table `tm` and every
    allocation of the current run (`log`). -/
def TagFrame (predSat : PredSat) (tm : TagMeaning) (log : List TagAlloc) : Prop :=
  ∃ P : TagMeaning, PredSatLaws predSat P ∧ tm ⊑ P ∧ LogIn log P

/-! ### Laws restrict to smaller tables -/

/-- The laws are anti-monotone in the table: a law for a table holds for every
    part of it. -/
theorem PredSatLaws.anti_mono {predSat : PredSat} {tm tm' : TagMeaning}
    (hsub : tm ⊑ tm') (h : PredSatLaws predSat tm') : PredSatLaws predSat tm :=
  ⟨fun condition ctx fuel k deps μ ρ θ addr pm registry cfg b hwf hmatch hric hterm =>
      h.match_iff condition ctx fuel k deps μ ρ θ addr pm registry cfg b
        (wfTagMeaningCtx_mono hsub hwf) hmatch hric hterm,
    h.mem_monotone⟩

/-! ### `LogIn` -/

theorem LogIn.sub {log log' : List TagAlloc} {P : TagMeaning}
    (h : LogIn log P) (hsub : ∀ a ∈ log', a ∈ log) : LogIn log' P :=
  fun a ha => h a (hsub a ha)

theorem LogIn.append {log₁ log₂ : List TagAlloc} {P : TagMeaning}
    (h₁ : LogIn log₁ P) (h₂ : LogIn log₂ P) : LogIn (log₁ ++ log₂) P := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h₁ a ha
  · exact h₂ a ha

theorem LogIn.left {log₁ log₂ : List TagAlloc} {P : TagMeaning}
    (h : LogIn (log₁ ++ log₂) P) : LogIn log₁ P :=
  fun a ha => h a (List.mem_append_left _ ha)

theorem LogIn.right {log₁ log₂ : List TagAlloc} {P : TagMeaning}
    (h : LogIn (log₁ ++ log₂) P) : LogIn log₂ P :=
  fun a ha => h a (List.mem_append_right _ ha)

theorem LogIn.of_log_eq {log log' : List TagAlloc} {P : TagMeaning}
    (h : LogIn log P) (heq : log = log') : LogIn log' P :=
  heq ▸ h

/-! ### `WithinLog` -/

theorem WithinLog.refl (tm : TagMeaning) (log : List TagAlloc) : WithinLog tm log tm :=
  fun _ _ h => Or.inl h

theorem WithinLog.mono_log {tm tm' : TagMeaning} {log log' : List TagAlloc}
    (h : WithinLog tm log tm') (hsub : ∀ a ∈ log, a ∈ log') : WithinLog tm log' tm' := by
  intro t d hd
  rcases h t d hd with h | ⟨a, ha, hat, had⟩
  · exact Or.inl h
  · exact Or.inr ⟨a, hsub a ha, hat, had⟩

theorem WithinLog.trans {tm tm₁ tm₂ : TagMeaning} {log log₁ log₂ : List TagAlloc}
    (h₁ : WithinLog tm log₁ tm₁) (h₂ : WithinLog tm₁ log₂ tm₂)
    (hsub₁ : ∀ a ∈ log₁, a ∈ log) (hsub₂ : ∀ a ∈ log₂, a ∈ log) :
    WithinLog tm log tm₂ := by
  intro t d hd
  rcases h₂ t d hd with h | ⟨a, ha, hat, had⟩
  · exact (h₁.mono_log hsub₁) t d h
  · exact Or.inr ⟨a, hsub₂ a ha, hat, had⟩

/-- A table built from `tm` with allocations of `log` is part of every table
    that contains `tm` and records `log`. -/
theorem WithinLog.submap {tm tm' P : TagMeaning} {log : List TagAlloc}
    (h : WithinLog tm log tm') (hsub : tm ⊑ P) (hlog : LogIn log P) : tm' ⊑ P := by
  intro t d hd
  rcases h t d hd with h | ⟨a, ha, hat, had⟩
  · exact hsub t d h
  · have := hlog a ha
    rw [hat, had] at this
    exact this

/-- Part of a table that adds only allocations of a log adds only allocations
    of that log. -/
theorem WithinLog.of_submap {tm tm' Q : TagMeaning} {log : List TagAlloc}
    (h : WithinLog tm log Q) (hsub : tm' ⊑ Q) : WithinLog tm log tm' :=
  fun t d hd => h t d (hsub t d hd)

/-! ### `TagFrame` -/

/-- The law at the current table. -/
theorem TagFrame.laws {predSat : PredSat} {tm : TagMeaning} {log : List TagAlloc}
    (h : TagFrame predSat tm log) : PredSatLaws predSat tm := by
  rcases h with ⟨P, hP, hsub, _⟩
  exact PredSatLaws.anti_mono hsub hP

/-- A frame for a run is a frame for each of its sub-runs. -/
theorem TagFrame.sub {predSat : PredSat} {tm : TagMeaning} {log log' : List TagAlloc}
    (h : TagFrame predSat tm log) (hsub : ∀ a ∈ log', a ∈ log) : TagFrame predSat tm log' := by
  rcases h with ⟨P, hP, hsubP, hlog⟩
  exact ⟨P, hP, hsubP, hlog.sub hsub⟩

/-- After a sub-run that added only allocations of its own log (`log₁`), the
    frame carries to the next sub-run (`log₂`), when both logs are part of the
    log of the enclosing run. -/
theorem TagFrame.step {predSat : PredSat} {tm tm₁ : TagMeaning}
    {log log₁ log₂ : List TagAlloc}
    (h : TagFrame predSat tm log) (hwithin : WithinLog tm log₁ tm₁)
    (hsub₁ : ∀ a ∈ log₁, a ∈ log) (hsub₂ : ∀ a ∈ log₂, a ∈ log) :
    TagFrame predSat tm₁ log₂ := by
  rcases h with ⟨P, hP, hsubP, hlog⟩
  exact ⟨P, hP, hwithin.submap hsubP (hlog.sub hsub₁), hlog.sub hsub₂⟩

/-- The law at a table the run built (`tm'`, within the run's log). -/
theorem TagFrame.laws_of_within {predSat : PredSat} {tm tm' : TagMeaning}
    {log : List TagAlloc}
    (h : TagFrame predSat tm log) (hwithin : WithinLog tm log tm') :
    PredSatLaws predSat tm' :=
  (h.step hwithin (fun _ ha => ha) (fun _ ha => ha)).laws

theorem TagFrame.left {predSat : PredSat} {tm : TagMeaning} {log₁ log₂ : List TagAlloc}
    (h : TagFrame predSat tm (log₁ ++ log₂)) : TagFrame predSat tm log₁ :=
  h.sub fun _ ha => List.mem_append_left _ ha

theorem TagFrame.right {predSat : PredSat} {tm : TagMeaning} {log₁ log₂ : List TagAlloc}
    (h : TagFrame predSat tm (log₁ ++ log₂)) : TagFrame predSat tm log₂ :=
  h.sub fun _ ha => List.mem_append_right _ ha

theorem TagFrame.of_log_eq {predSat : PredSat} {tm : TagMeaning} {log log' : List TagAlloc}
    (h : TagFrame predSat tm log) (heq : log = log') : TagFrame predSat tm log' :=
  heq ▸ h

/-- After the first of two sub-runs in sequence, the frame carries to the
    second, from the table the first built. -/
theorem TagFrame.next {predSat : PredSat} {tm tm₁ : TagMeaning} {log₁ log₂ : List TagAlloc}
    (h : TagFrame predSat tm (log₁ ++ log₂)) (hwithin : WithinLog tm log₁ tm₁) :
    TagFrame predSat tm₁ log₂ :=
  h.step hwithin (fun _ ha => List.mem_append_left _ ha) (fun _ ha => List.mem_append_right _ ha)

/-- The third of three sub-runs, from the table the first built (the second
    is an alternative to the third, not a predecessor). -/
theorem TagFrame.skip {predSat : PredSat} {tm tm₁ : TagMeaning}
    {log₁ log₂ log₃ : List TagAlloc}
    (h : TagFrame predSat tm (log₁ ++ log₂ ++ log₃)) (hwithin : WithinLog tm log₁ tm₁) :
    TagFrame predSat tm₁ log₃ :=
  h.step hwithin (fun _ ha => List.mem_append_left _ (List.mem_append_left _ ha))
    (fun _ ha => List.mem_append_right _ ha)

/-- Two tables built in sequence add only allocations of the two logs. -/
theorem WithinLog.append {tm tm₁ tm₂ : TagMeaning} {log₁ log₂ : List TagAlloc}
    (h₁ : WithinLog tm log₁ tm₁) (h₂ : WithinLog tm₁ log₂ tm₂) :
    WithinLog tm (log₁ ++ log₂) tm₂ :=
  h₁.trans h₂ (fun _ ha => List.mem_append_left _ ha) (fun _ ha => List.mem_append_right _ ha)

theorem WithinLog.of_log_eq {tm tm' : TagMeaning} {log log' : List TagAlloc}
    (h : WithinLog tm log tm') (heq : log = log') : WithinLog tm log' tm' :=
  heq ▸ h

/-! ### `LogFresh` -/

theorem LogFresh.nil (lo hi : Tag) : LogFresh lo hi [] := by
  constructor <;> simp

theorem LogFresh.mono {lo hi lo' hi' : Tag} {log : List TagAlloc}
    (h : LogFresh lo hi log) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : LogFresh lo' hi' log :=
  ⟨fun a ha => ⟨Nat.le_trans hlo (h.1 a ha).1, Nat.lt_of_lt_of_le (h.1 a ha).2 hhi⟩, h.2⟩

theorem LogFresh.append {lo mid hi : Tag} {log₁ log₂ : List TagAlloc}
    (h₁ : LogFresh lo mid log₁) (h₂ : LogFresh mid hi log₂)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi) : LogFresh lo hi (log₁ ++ log₂) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨(h₁.1 a ha).1, Nat.lt_of_lt_of_le (h₁.1 a ha).2 hhi⟩
    · exact ⟨Nat.le_trans hlo (h₂.1 a ha).1, (h₂.1 a ha).2⟩
  · intro a ha b hb hab
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact h₁.2 a ha b hb hab
    · exact absurd hab (Nat.ne_of_lt (Nat.lt_of_lt_of_le (h₁.1 a ha).2 (h₂.1 b hb).1))
    · exact absurd hab (Nat.ne_of_gt (Nat.lt_of_lt_of_le (h₁.1 b hb).2 (h₂.1 a ha).1))
    · exact h₂.2 a ha b hb hab

/-! ### Program tables -/

private theorem programTable_lookup_of_not_mem (tm : TagMeaning) (log : List TagAlloc)
    (t : Tag) (hnot : ∀ a ∈ log, a.tag ≠ t) :
    (programTable tm log).lookup t = tm.lookup t := by
  induction log generalizing tm with
  | nil => rfl
  | cons a rest ih =>
      simp only [programTable, List.foldl_cons]
      have hrest : ∀ b ∈ rest, b.tag ≠ t := fun b hb => hnot b (List.mem_cons_of_mem _ hb)
      rw [show List.foldl (fun acc a => acc.update a.tag a.desc) (tm.update a.tag a.desc) rest =
          programTable (tm.update a.tag a.desc) rest from rfl, ih _ hrest]
      have hne : a.tag ≠ t := hnot a (List.mem_cons_self ..)
      show (tm.insert a.tag a.desc).get? t = tm.get? t
      rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert]
      have hcmp : compare a.tag t ≠ Ordering.eq := by
        intro h
        exact hne (LawfulEqCmp.eq_of_compare h)
      simp [hcmp]

private theorem programTable_lookup_of_mem (tm : TagMeaning) (log : List TagAlloc)
    (hcons : ∀ a ∈ log, ∀ b ∈ log, a.tag = b.tag → a = b)
    (a : TagAlloc) (ha : a ∈ log) :
    (programTable tm log).lookup a.tag = some a.desc := by
  induction log generalizing tm with
  | nil => cases ha
  | cons b rest ih =>
      simp only [programTable, List.foldl_cons]
      rw [show List.foldl (fun acc a => acc.update a.tag a.desc) (tm.update b.tag b.desc) rest =
          programTable (tm.update b.tag b.desc) rest from rfl]
      have hcons' : ∀ x ∈ rest, ∀ y ∈ rest, x.tag = y.tag → x = y :=
        fun x hx y hy hxy =>
          hcons x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy
      by_cases harest : a ∈ rest
      · exact ih _ hcons' harest
      · have hab : a = b := by
          rcases List.mem_cons.mp ha with h | h
          · exact h
          · exact absurd h harest
        subst hab
        by_cases hlater : ∃ c ∈ rest, c.tag = a.tag
        · rcases hlater with ⟨c, hc, hct⟩
          have hca : c = a := hcons c (List.mem_cons_of_mem _ hc) a ha hct
          subst hca
          exact absurd hc harest
        · have hnot : ∀ c ∈ rest, c.tag ≠ a.tag := by
            intro c hc hct
            exact hlater ⟨c, hc, hct⟩
          rw [programTable_lookup_of_not_mem _ rest a.tag hnot]
          show (tm.insert a.tag a.desc).get? a.tag = some a.desc
          rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert]
          simp

/-- The program table records every allocation of a log whose tags determine
    its allocations. -/
theorem programTable_logIn (tm : TagMeaning) (log : List TagAlloc)
    (hcons : ∀ a ∈ log, ∀ b ∈ log, a.tag = b.tag → a = b) :
    LogIn log (programTable tm log) :=
  fun a ha => programTable_lookup_of_mem tm log hcons a ha

/-- The starting table is part of the program table when the log allocates
    only tags the table does not bind. -/
theorem programTable_extends (tm : TagMeaning) (log : List TagAlloc) (lo : Tag)
    (hbounded : TagMeaningBounded tm lo) (hfresh : ∀ a ∈ log, lo ≤ a.tag) :
    tm ⊑ programTable tm log := by
  intro t d hd
  have hlt : t < lo := hbounded t d hd
  have hnot : ∀ a ∈ log, a.tag ≠ t := by
    intro a ha hat
    have := hfresh a ha
    rw [hat] at this
    exact Nat.not_le.mpr hlt this
  show (programTable tm log).lookup t = some d
  rw [programTable_lookup_of_not_mem tm log t hnot]
  exact hd

/-- The program table adds to the starting table only allocations of the log. -/
theorem programTable_within (tm : TagMeaning) (log : List TagAlloc) :
    WithinLog tm log (programTable tm log) := by
  induction log generalizing tm with
  | nil => exact WithinLog.refl tm []
  | cons a rest ih =>
      intro t d hd
      simp only [programTable, List.foldl_cons] at hd
      rcases ih (tm.update a.tag a.desc) t d hd with h | ⟨b, hb, hbt, hbd⟩
      · by_cases hat : a.tag = t
        · subst hat
          have : (tm.update a.tag a.desc).lookup a.tag = some a.desc := by
            show (tm.insert a.tag a.desc).get? a.tag = some a.desc
            rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert]
            simp
          rw [this] at h
          exact Or.inr ⟨a, List.mem_cons_self .., rfl, Option.some.inj h⟩
        · left
          have hcmp : compare a.tag t ≠ Ordering.eq := by
            intro h
            exact hat (LawfulEqCmp.eq_of_compare h)
          have : (tm.update a.tag a.desc).lookup t = tm.lookup t := by
            show (tm.insert a.tag a.desc).get? t = tm.get? t
            rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.get?_eq_getElem?,
              ExtTreeMap.getElem?_insert]
            simp [hcmp]
          rw [this] at h
          exact h
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hbt, hbd⟩

/-- The frame of a whole run: a law at the program table of a run whose log is
    fresh above the starting table gives the frame for that run. -/
theorem TagFrame.of_programTable {predSat : PredSat} {tm : TagMeaning}
    {log : List TagAlloc} {lo hi : Tag}
    (hlaws : PredSatLaws predSat (programTable tm log))
    (hbounded : TagMeaningBounded tm lo) (hfresh : LogFresh lo hi log) :
    TagFrame predSat tm log :=
  ⟨programTable tm log, hlaws,
    programTable_extends tm log lo hbounded (fun a ha => (hfresh.1 a ha).1),
    programTable_logIn tm log hfresh.2⟩

/-! ### Extern allocation batches -/

/-- Semantic predicate: the tag mapping produced by `collectAndAllocExternTags`
    is consistent with `tm`.  For every allocated tag that corresponds to a
    `guardClosure` predicate whose body successfully converts to `PExpr`, the
    tag meaning maps that tag to the expected guard descriptor. -/
def TagMappingRespectsTagMeaning (tm : TagMeaning)
    (mapping : TagMapping)
    (preds : List SyntaxPredicate) (env : VarTypeEnv) : Prop :=
  ∀ idx tag, mapping.get? idx = some tag →
    ∀ arg body pbody,
      (SyntaxPredicate.guardClosure idx arg body) ∈ preds →
      body.toPExpr = .ok pbody →
      tm.lookup tag = some { argName := arg, body := pbody,
                             capEnv := VarTypeEnv.toCaptured env }

/-- `tm'` is the canonical tag-meaning extension for one extern allocation
    batch produced by `collectAndAllocExternTags`.  This is a *structural*
    predicate: it records that `tm'` extends `tm`, is bounded by the new
    fresh-tag cursor, and matches every resolved `guardClosure` allocated by
    the batch, and adds to `tm` only the allocations the batch logs
    (`externTagLog`).  It carries no `predSat` content. -/
def ExternBatchTagMeaningExtension
    (tm : TagMeaning) (nextTag : Tag)
    (mapping : TagMapping) (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (nextTag' : Tag) (tm' : TagMeaning) : Prop :=
  tm ⊑ tm' ∧
  TagMeaningBounded tm' nextTag' ∧
  TagMappingRespectsTagMeaning tm' mapping preds env ∧
  nextTag ≤ nextTag' ∧
  WithinLog tm (externTagLog preds env mapping) tm'

namespace ExternBatchTagMeaningExtension

/-- The submap projection. -/
theorem extends_tm
    {tm : TagMeaning} {nextTag : Tag} {mapping : TagMapping}
    {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {nextTag' : Tag} {tm' : TagMeaning}
    (h : ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm') :
    tm ⊑ tm' :=
  h.1

/-- The boundedness projection. -/
theorem bounded
    {tm : TagMeaning} {nextTag : Tag} {mapping : TagMapping}
    {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {nextTag' : Tag} {tm' : TagMeaning}
    (h : ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm') :
    TagMeaningBounded tm' nextTag' :=
  h.2.1

/-- The structural compatibility projection for the canonical extension. -/
theorem respects
    {tm : TagMeaning} {nextTag : Tag} {mapping : TagMapping}
    {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {nextTag' : Tag} {tm' : TagMeaning}
    (h : ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm') :
    TagMappingRespectsTagMeaning tm' mapping preds env :=
  h.2.2.1

/-- The extension adds only allocations the batch logs. -/
theorem within
    {tm : TagMeaning} {nextTag : Tag} {mapping : TagMapping}
    {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {nextTag' : Tag} {tm' : TagMeaning}
    (h : ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm') :
    WithinLog tm (externTagLog preds env mapping) tm' :=
  h.2.2.2.2


end ExternBatchTagMeaningExtension

private def buildBatchTmStep (mapping : TagMapping) (env : VarTypeEnv)
    (acc : TagMeaning) (pred : SyntaxPredicate) : TagMeaning :=
  match pred with
  | SyntaxPredicate.guardClosure idx arg body =>
      match mapping.get? idx, body.toPExpr with
      | some tag, .ok pbody =>
          acc.update tag { argName := arg, body := pbody,
                           capEnv := VarTypeEnv.toCaptured env }
      | _, _ => acc
  | _ => acc

private def buildBatchTm (tm : TagMeaning) (mapping : TagMapping)
    (preds : List SyntaxPredicate) (env : VarTypeEnv) : TagMeaning :=
  preds.foldl (buildBatchTmStep mapping env) tm

/-- The canonical batch table is the program table of the batch log. -/
private lemma buildBatchTm_eq_programTable (tm : TagMeaning) (mapping : TagMapping)
    (preds : List SyntaxPredicate) (env : VarTypeEnv) :
    buildBatchTm tm mapping preds env = programTable tm (externTagLog preds env mapping) := by
  induction preds generalizing tm with
  | nil => rfl
  | cons pred rest ih =>
      have hstep : buildBatchTm tm mapping (pred :: rest) env =
          buildBatchTm (buildBatchTmStep mapping env tm pred) mapping rest env := rfl
      rw [hstep, ih]
      cases pred with
      | guardClosure idx arg body =>
          cases hget : mapping.get? idx with
          | none =>
              rw [ExtTreeMap.get?_eq_getElem?] at hget
              simp [buildBatchTmStep, externTagLog, hget]
          | some tag =>
              rw [ExtTreeMap.get?_eq_getElem?] at hget
              cases hbody : body.toPExpr with
              | error err =>
                  simp [buildBatchTmStep, externTagLog, hget, hbody]
              | ok pbody =>
                  simp [buildBatchTmStep, externTagLog, hget, hbody, programTable,
                    TagAlloc.desc]
      | guardOnly idx => simp [buildBatchTmStep, externTagLog]
      | noPred => simp [buildBatchTmStep, externTagLog]

private lemma TagMeaning.lookup_update_self
    (tm : TagMeaning) (tag : Tag) (desc : GuardDesc) :
    (tm.update tag desc).lookup tag = some desc := by
  show (tm.insert tag desc).get? tag = some desc
  rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.getElem?_insert]
  simp

private lemma TagMeaning.lookup_update_ne
    (tm : TagMeaning) {tag tag' : Tag} (desc : GuardDesc)
    (hne : tag' ≠ tag) :
    (tm.update tag' desc).lookup tag = tm.lookup tag := by
  have hcmp : compare tag' tag ≠ Ordering.eq := by
    intro h
    exact hne (LawfulEqCmp.eq_of_compare h)
  show (tm.insert tag' desc).get? tag = tm.get? tag
  rw [ExtTreeMap.get?_eq_getElem?, ExtTreeMap.get?_eq_getElem?]
  rw [ExtTreeMap.getElem?_insert]
  simp [hcmp]

private lemma buildBatchTm_fold_preserves_lookup
    (acc : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {nextTag k : Tag} {d : GuardDesc}
    (hk_lt : k < nextTag)
    (h_alloc_ge : ∀ idx tag, mapping.get? idx = some tag → nextTag ≤ tag)
    (hlookup : acc.lookup k = some d) :
    (preds.foldl (buildBatchTmStep mapping env) acc).lookup k = some d := by
  induction preds generalizing acc with
  | nil =>
      simpa using hlookup
  | cons pred rest ih =>
      simp [List.foldl, buildBatchTmStep]
      cases pred with
      | noPred =>
          simpa [buildBatchTmStep] using ih acc hlookup
      | guardOnly _ =>
          simpa [buildBatchTmStep] using ih acc hlookup
      | guardClosure idx arg body =>
          cases hmap : mapping.get? idx <;> cases hbody : body.toPExpr
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup
          · rename_i tag _err
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup
          · rename_i tag pbody
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            set desc : GuardDesc :=
              { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } with hdesc
            have htag_ge : nextTag ≤ tag := h_alloc_ge idx tag hmap
            have hne : tag ≠ k := by
              intro hEq
              subst hEq
              exact Nat.not_le_of_gt hk_lt htag_ge
            have hlookup' : (acc.update tag desc).lookup k = some d := by
              rw [TagMeaning.lookup_update_ne acc desc hne]
              exact hlookup
            simpa [buildBatchTmStep, hmap', hbody, hdesc] using
              ih (acc.update tag desc) hlookup'

private lemma buildBatchTm_preserves_input_lookup
    (tm : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {nextTag : Tag}
    (h_bounded : TagMeaningBounded tm nextTag)
    (h_alloc_ge : ∀ idx tag, mapping.get? idx = some tag → nextTag ≤ tag) :
    tm ⊑ buildBatchTm tm mapping preds env := by
  intro k d hlookup
  exact buildBatchTm_fold_preserves_lookup tm mapping preds env
    (h_bounded k d hlookup) h_alloc_ge hlookup

private lemma TagMeaningBounded.update_lt
    {tm : TagMeaning} {bound tag : Tag} (h : TagMeaningBounded tm bound)
    (desc : GuardDesc) (htag : tag < bound) :
    TagMeaningBounded (tm.update tag desc) bound := by
  intro k d hlookup
  by_cases hEq : tag = k
  · subst hEq
    rw [TagMeaning.lookup_update_self] at hlookup
    cases hlookup
    exact htag
  · rw [TagMeaning.lookup_update_ne tm desc hEq] at hlookup
    exact h k d hlookup

private lemma buildBatchTm_fold_bounded
    (acc : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {bound : Tag}
    (h_acc : TagMeaningBounded acc bound)
    (h_alloc_lt : ∀ idx tag, mapping.get? idx = some tag → tag < bound) :
    TagMeaningBounded (preds.foldl (buildBatchTmStep mapping env) acc) bound := by
  induction preds generalizing acc with
  | nil =>
      simpa using h_acc
  | cons pred rest ih =>
      simp [List.foldl, buildBatchTmStep]
      cases pred with
      | noPred =>
          simpa [buildBatchTmStep] using ih acc h_acc
      | guardOnly _ =>
          simpa [buildBatchTmStep] using ih acc h_acc
      | guardClosure idx arg body =>
          cases hmap : mapping.get? idx <;> cases hbody : body.toPExpr
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc h_acc
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc h_acc
          · rename_i tag _err
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc h_acc
          · rename_i tag pbody
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            set desc : GuardDesc :=
              { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } with hdesc
            have h_acc' : TagMeaningBounded (acc.update tag desc) bound :=
              h_acc.update_lt desc (h_alloc_lt idx tag hmap)
            simpa [buildBatchTmStep, hmap', hbody, hdesc] using ih (acc.update tag desc) h_acc'

private lemma buildBatchTm_bounded
    (tm : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {nextTag nextTag' : Tag}
    (h_bounded : TagMeaningBounded tm nextTag)
    (h_le : nextTag ≤ nextTag')
    (h_alloc_lt : ∀ idx tag, mapping.get? idx = some tag → tag < nextTag') :
    TagMeaningBounded (buildBatchTm tm mapping preds env) nextTag' := by
  unfold buildBatchTm
  exact buildBatchTm_fold_bounded tm mapping preds env (h_bounded.mono h_le) h_alloc_lt

private lemma buildBatchTm_fold_preserves_lookup_of_compatible
    (acc : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv) {tag : Tag} {desc : GuardDesc}
    (hlookup : acc.lookup tag = some desc)
    (hcompat : ∀ {idx : TagIndex} {arg : Name} {body : Expr} {pbody : PExpr},
      SyntaxPredicate.guardClosure idx arg body ∈ preds →
      mapping.get? idx = some tag →
      body.toPExpr = .ok pbody →
      desc = { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env }) :
    (preds.foldl (buildBatchTmStep mapping env) acc).lookup tag = some desc := by
  induction preds generalizing acc with
  | nil =>
      simpa using hlookup
  | cons pred rest ih =>
      simp [List.foldl, buildBatchTmStep]
      have hcompat_tail :
          ∀ {idx : TagIndex} {arg : Name} {body : Expr} {pbody : PExpr},
            SyntaxPredicate.guardClosure idx arg body ∈ rest →
            mapping.get? idx = some tag →
            body.toPExpr = .ok pbody →
            desc = { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } := by
        intro idx arg body pbody hmem hmap hbody
        exact hcompat (List.mem_cons_of_mem pred hmem) hmap hbody
      cases pred with
      | noPred =>
          simpa [buildBatchTmStep] using ih acc hlookup hcompat_tail
      | guardOnly _ =>
          simpa [buildBatchTmStep] using ih acc hlookup hcompat_tail
      | guardClosure idx arg body =>
          cases hmap : mapping.get? idx <;> cases hbody : body.toPExpr
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup hcompat_tail
          · have hmap' : mapping[idx]? = none := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup hcompat_tail
          · rename_i tag' _err
            have hmap' : mapping[idx]? = some tag' := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            simpa [buildBatchTmStep, hmap', hbody] using ih acc hlookup hcompat_tail
          · rename_i tag' pbody
            have hmap' : mapping[idx]? = some tag' := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            set desc' : GuardDesc :=
              { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } with hdesc'
            have hlookup' : (acc.update tag' desc').lookup tag = some desc := by
              by_cases htag : tag' = tag
              · subst htag
                have hdesc_eq : desc = desc' := by
                  simpa [hdesc'] using
                    (hcompat (by simp) hmap hbody)
                rw [TagMeaning.lookup_update_self]
                exact congrArg some hdesc_eq.symm
              · rw [TagMeaning.lookup_update_ne acc desc' htag]
                exact hlookup
            simpa [buildBatchTmStep, hmap', hbody, hdesc'] using
              ih (acc.update tag' desc') hlookup' hcompat_tail

private lemma buildBatchTm_fold_lookup_of_guard_mem
    (acc : TagMeaning) (mapping : TagMapping) (preds : List SyntaxPredicate)
    (env : VarTypeEnv)
    (h_cons : ∀ {idx : TagIndex} {arg₁ arg₂ : Name} {body₁ body₂ : Expr},
      SyntaxPredicate.guardClosure idx arg₁ body₁ ∈ preds →
      SyntaxPredicate.guardClosure idx arg₂ body₂ ∈ preds →
      arg₁ = arg₂ ∧ body₁ = body₂)
    (h_inj : ∀ (idx₁ idx₂ : TagIndex) (tag : Tag),
      mapping.get? idx₁ = some tag → mapping.get? idx₂ = some tag → idx₁ = idx₂)
    {idx : TagIndex} {tag : Tag} {arg : Name} {body : Expr} {pbody : PExpr}
    (hmap : mapping.get? idx = some tag)
    (hmem : SyntaxPredicate.guardClosure idx arg body ∈ preds)
    (hbody : body.toPExpr = .ok pbody) :
    (preds.foldl (buildBatchTmStep mapping env) acc).lookup tag =
      some { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } := by
  induction preds generalizing acc with
  | nil =>
      cases hmem
  | cons pred rest ih =>
      simp only [List.foldl]
      simp only [List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · cases pred with
        | noPred => cases hhead
        | guardOnly _ => cases hhead
        | guardClosure idx₀ arg₀ body₀ =>
            have h_eqs :=
              (SyntaxPredicate.guardClosure.injEq idx arg body idx₀ arg₀ body₀).mp hhead
            obtain ⟨hidx, harg, hbody_expr⟩ := h_eqs
            subst idx₀
            subst arg₀
            subst body₀
            have hmap' : mapping[idx]? = some tag := by
              rwa [← ExtTreeMap.get?_eq_getElem?]
            set desc : GuardDesc :=
              { argName := arg, body := pbody, capEnv := VarTypeEnv.toCaptured env } with hdesc
            have hlookup_head :
                (buildBatchTmStep mapping env acc
                    (SyntaxPredicate.guardClosure idx arg body)).lookup tag = some desc := by
              simp [buildBatchTmStep, hmap', hbody, hdesc, TagMeaning.lookup_update_self]
            have hcompat_tail :
                ∀ {idx' : TagIndex} {arg' : Name} {body' : Expr} {pbody' : PExpr},
                  SyntaxPredicate.guardClosure idx' arg' body' ∈ rest →
                  mapping.get? idx' = some tag →
                  body'.toPExpr = .ok pbody' →
                  desc = { argName := arg', body := pbody',
                           capEnv := VarTypeEnv.toCaptured env } := by
              intro idx' arg' body' pbody' hmem' hmap' hbody'
              have hidx' : idx' = idx := h_inj idx' idx tag hmap' hmap
              subst idx'
              have hhead_mem :
                  SyntaxPredicate.guardClosure idx arg body ∈
                    SyntaxPredicate.guardClosure idx arg body :: rest :=
                List.Mem.head rest
              have hagree := h_cons (List.mem_cons_of_mem _ hmem') hhead_mem
              have harg' : arg' = arg := hagree.1
              have hbody_expr' : body' = body := hagree.2
              subst arg'
              subst body'
              have hpbody : pbody' = pbody := by
                rw [hbody] at hbody'
                exact (Except.ok.inj hbody').symm
              subst pbody'
              rfl
            unfold buildBatchTmStep at hlookup_head
            simpa [hdesc] using
              buildBatchTm_fold_preserves_lookup_of_compatible
                (buildBatchTmStep mapping env acc (SyntaxPredicate.guardClosure idx arg body))
                mapping rest env hlookup_head hcompat_tail
      · have h_cons_tail :
            ∀ {idx : TagIndex} {arg₁ arg₂ : Name} {body₁ body₂ : Expr},
              SyntaxPredicate.guardClosure idx arg₁ body₁ ∈ rest →
              SyntaxPredicate.guardClosure idx arg₂ body₂ ∈ rest →
              arg₁ = arg₂ ∧ body₁ = body₂ := by
          intro idx arg₁ arg₂ body₁ body₂ hmem₁ hmem₂
          exact h_cons (List.mem_cons_of_mem pred hmem₁) (List.mem_cons_of_mem pred hmem₂)
        exact ih (buildBatchTmStep mapping env acc pred) h_cons_tail htail

/-- Canonical extension for a general extern batch: given a successful
    `collectAndAllocExternTags` run and an input table bounded by the
    incoming fresh-tag cursor, construct the canonical tag-meaning table
    for the whole batch. -/
theorem ExternBatchTagMeaningExtension.canonical_general
    (tm : TagMeaning) (preds : List SyntaxPredicate) (env : VarTypeEnv)
    (mapping : TagMapping) (nextTag nextTag' : Tag)
    (h_bounded : TagMeaningBounded tm nextTag)
    (h_alloc : collectAndAllocExternTags preds nextTag = .ok (mapping, nextTag')) :
    ∃ tm', ExternBatchTagMeaningExtension tm nextTag mapping preds env nextTag' tm' := by
  let tm' := buildBatchTm tm mapping preds env
  have h_le : nextTag ≤ nextTag' :=
    collectAndAllocExternTags_nextTag_ge preds nextTag mapping nextTag' h_alloc
  have h_alloc_ge : ∀ idx tag, mapping.get? idx = some tag → nextTag ≤ tag := by
    intro idx tag hget
    exact collectAndAllocExternTags_mapping_values_ge preds nextTag mapping nextTag'
      h_alloc idx tag hget
  have h_alloc_lt : ∀ idx tag, mapping.get? idx = some tag → tag < nextTag' := by
    intro idx tag hget
    exact collectAndAllocExternTags_mapping_values_lt preds nextTag mapping nextTag'
      h_alloc idx tag hget
  have h_cons :
      ∀ {idx : TagIndex} {arg₁ arg₂ : Name} {body₁ body₂ : Expr},
        SyntaxPredicate.guardClosure idx arg₁ body₁ ∈ preds →
        SyntaxPredicate.guardClosure idx arg₂ body₂ ∈ preds →
        arg₁ = arg₂ ∧ body₁ = body₂ := by
    intro idx arg₁ arg₂ body₁ body₂ hmem₁ hmem₂
    exact collectAndAllocExternTags_consistent_preds preds nextTag mapping nextTag'
      h_alloc hmem₁ hmem₂
  have h_inj :
      ∀ (idx₁ idx₂ : TagIndex) (tag : Tag),
        mapping.get? idx₁ = some tag → mapping.get? idx₂ = some tag → idx₁ = idx₂ := by
    intro idx₁ idx₂ tag hget₁ hget₂
    exact collectAndAllocExternTags_mapping_values_injective preds nextTag mapping nextTag'
      h_alloc idx₁ idx₂ tag hget₁ hget₂
  refine ⟨tm', ?_, ?_, ?_, h_le, ?_⟩
  · exact buildBatchTm_preserves_input_lookup tm mapping preds env h_bounded h_alloc_ge
  · exact buildBatchTm_bounded tm mapping preds env h_bounded h_le h_alloc_lt
  · intro idx tag hmap arg body pbody hmem hbody
    simpa [tm', buildBatchTm] using
      buildBatchTm_fold_lookup_of_guard_mem tm mapping preds env h_cons h_inj
        hmap hmem hbody
  · rw [show tm' = programTable tm (externTagLog preds env mapping) from
      buildBatchTm_eq_programTable tm mapping preds env]
    exact programTable_within tm (externTagLog preds env mapping)

-- Freshness of typing-run logs

local macro "leaf_log" h:ident : tactic => `(tactic| (
  (try simp only [bind, Except.bind, pure, Except.pure] at $h:ident)
  repeat' split at $h:ident
  all_goals (try simp only [bind, Except.bind, pure, Except.pure, MonadExceptOf.throw, throwThe,
    Except.ok.injEq, reduceCtorEq] at $h:ident)
  all_goals (first | (subst $h:ident; rfl) | (cases $h:ident; rfl) | (cases $h:ident) | skip)))

private theorem typecheckVar_tagLog (ctx : TypeContext) (x : Name) (res : TypeResult)
    (h : typecheckVar ctx x = .ok res) : res.tagLog' = [] := by
  unfold typecheckVar at h
  leaf_log h

private theorem typecheckExternFn_tagLog (ctx : TypeContext) id arg argTyp argPoison argPred retSpec effects captures (res : TypeResult)
    (h : typecheckExternFn ctx id arg argTyp argPoison argPred retSpec effects captures = .ok res) : res.tagLog' = [] := by
  unfold typecheckExternFn at h
  leaf_log h

private theorem typecheckExternPfn_tagLog (ctx : TypeContext) id arg argTyp argPoison argPred retSpec captures (res : TypeResult)
    (h : typecheckExternPfn ctx id arg argTyp argPoison argPred retSpec captures = .ok res) : res.tagLog' = [] := by
  unfold typecheckExternPfn at h
  leaf_log h

private theorem typecheckExternRef_tagLog (ctx : TypeContext) id rp rpred cp cpred (res : TypeResult)
    (h : typecheckExternRef ctx id rp rpred cp cpred = .ok res) : res.tagLog' = [] := by
  unfold typecheckExternRef at h
  leaf_log h

private theorem typecheckFn_tagLog (ctx : TypeContext) x st1 body st2 (res : TypeResult)
    (h : typecheckFn ctx x st1 body st2 = .ok res) : res.tagLog' = [] := by
  unfold typecheckFn at h
  leaf_log h

private theorem typecheckPfn_tagLog (ctx : TypeContext) x st1 body st2 (res : TypeResult)
    (h : typecheckPfn ctx x st1 body st2 = .ok res) : res.tagLog' = [] := by
  unfold typecheckPfn at h
  leaf_log h

private theorem mem_externTagLog {preds : List SyntaxPredicate} {env : VarTypeEnv}
    {m : ExtTreeMap TagIndex Tag} {a : TagAlloc} (ha : a ∈ externTagLog preds env m) :
    ∃ idx body, SyntaxPredicate.guardClosure idx a.argName body ∈ preds ∧
      m.get? idx = some a.tag ∧ body.toPExpr = .ok a.body ∧
      a.capEnv = VarTypeEnv.toCaptured env := by
  simp only [externTagLog, List.mem_filterMap] at ha
  obtain ⟨pred, hpred, hsome⟩ := ha
  cases pred with
  | guardClosure idx arg body =>
      simp only at hsome
      split at hsome
      · rename_i tag pbody hget hpe
        cases hsome
        exact ⟨idx, body, hpred, hget, hpe, rfl⟩
      · cases hsome
  | guardOnly _ => cases hsome
  | noPred => cases hsome

private theorem externTagLog_logFresh (preds : List SyntaxPredicate) (env : VarTypeEnv) (t t' : Tag)
    (m : ExtTreeMap TagIndex Tag)
    (hc : collectAndAllocExternTags preds t = .ok (m, t')) :
    LogFresh t t' (externTagLog preds env m) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨idx, _body, _hmem, hget, _, _⟩ := mem_externTagLog ha
    exact ⟨collectAndAllocExternTags_mapping_values_ge preds t m t' hc idx a.tag hget,
      collectAndAllocExternTags_mapping_values_lt preds t m t' hc idx a.tag hget⟩
  · intro a ha b hb hab
    obtain ⟨idx₁, body₁, hmem₁, hget₁, hpe₁, hcap₁⟩ := mem_externTagLog ha
    obtain ⟨idx₂, body₂, hmem₂, hget₂, hpe₂, hcap₂⟩ := mem_externTagLog hb
    rw [hab] at hget₁
    have hidx : idx₁ = idx₂ :=
      collectAndAllocExternTags_mapping_values_injective preds t m t' hc idx₁ idx₂ b.tag hget₁ hget₂
    subst hidx
    obtain ⟨harg, hbody⟩ := collectAndAllocExternTags_consistent_preds preds t m t' hc hmem₁ hmem₂
    subst hbody
    rw [hpe₁] at hpe₂
    cases a; cases b
    simp only at hab harg hpe₂ hcap₁ hcap₂
    cases hpe₂
    subst hab harg
    rw [hcap₁, hcap₂]

private theorem externTagLog_logFresh' (preds : List SyntaxPredicate) (env : VarTypeEnv) (t : Tag)
    (v : ExtTreeMap TagIndex Tag × Tag)
    (hc : collectAndAllocExternTags preds t = .ok v) :
    LogFresh t v.2 (externTagLog preds env v.1) :=
  externTagLog_logFresh preds env t v.2 v.1 hc

private theorem applyFnTClosureAtCursor_logFresh
    (tcl : FnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (cursor : Tag × Loc) (fuel : Nat) (r : TypeResult)
    (IH : ∀ (ctx' : TypeContext) (e : Expr) (res' : TypeResult),
      typecheckExpr ctx' e fuel = .ok res' → LogFresh ctx'.nextTag res'.nextTag' res'.tagLog')
    (h : applyFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 cursor
      (fuel + 1) = .ok r) :
    LogFresh cursor.1 r.nextTag' r.tagLog' := by
  unfold applyFnTClosureAtCursor at h
  cases tcl with
  | regular x body env =>
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i v hv
        have hlog := IH _ _ _ hv
        simp only at hlog
        repeat' split at h
        all_goals (try simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h)
        all_goals (subst h; exact hlog)
  | extern id x retSpec effects capturedEnv declaredArgQt captures =>
      simp only [bind, Except.bind, pure, Except.pure, resolveArgCondQTyp] at h
      repeat' split at h
      all_goals (try simp only [Except.ok.injEq, reduceCtorEq] at h)
      all_goals (cases h)
      all_goals (try (exfalso; have hthrow := ‹throw _ = Except.ok _›; cases hthrow))
      all_goals (try (rename_i heqLast; split at heqLast <;>
        (try simp only [Except.ok.injEq, reduceCtorEq] at heqLast); (try subst heqLast)))
      all_goals (have hc := ‹collectAndAllocExternTags _ _ = Except.ok _›
                 simpa using externTagLog_logFresh' _ _ _ _ hc)

private theorem applyPFnTClosureAtCursor_logFresh
    (tcl : PFnTClosure) (st1 st2 : Typ) (p p1 : Poison)
    (argEtyp : ETyp) (argPoison : Poison) (argPred : Predicate)
    (ctx : TypeContext) (result2 : TypeResult) (cursor : Tag × Loc) (fuel : Nat) (r : TypeResult)
    (IH : ∀ (ctx' : TypeContext) (e : Expr) (res' : TypeResult),
      typecheckExpr ctx' e fuel = .ok res' → LogFresh ctx'.nextTag res'.nextTag' res'.tagLog')
    (h : applyPFnTClosureAtCursor tcl st1 st2 p p1 argEtyp argPoison argPred ctx result2 cursor
      (fuel + 1) = .ok r) :
    LogFresh cursor.1 r.nextTag' r.tagLog' := by
  unfold applyPFnTClosureAtCursor at h
  cases tcl with
  | regular x body env =>
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i v hv
        have hlog := IH _ _ _ hv
        simp only at hlog
        repeat' split at h
        all_goals (try simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq] at h)
        all_goals (subst h; exact hlog)
  | extern id x retSpec capturedEnv declaredArgQt captures =>
      simp only [bind, Except.bind, pure, Except.pure, resolveArgCondQTyp] at h
      repeat' split at h
      all_goals (try simp only [Except.ok.injEq, reduceCtorEq] at h)
      all_goals (cases h)
      all_goals (try (exfalso; have hthrow := ‹throw _ = Except.ok _›; cases hthrow))
      all_goals (try (rename_i heqLast; split at heqLast <;>
        (try simp only [Except.ok.injEq, reduceCtorEq] at heqLast); (try subst heqLast)))
      all_goals (first
        | (have hc := ‹collectAndAllocExternTags _ _ = Except.ok _›
           simpa using externTagLog_logFresh' _ _ _ _ hc)
        | simpa using LogFresh.nil cursor.1 cursor.1)

theorem joinTypeResults_tagLog (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult)
    (res : TypeResult) (h : joinTypeResults ctx first rest = .ok res) :
    res.tagLog' = first.tagLog' ++ rest.flatMap (·.tagLog') := by
  unfold joinTypeResults at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (try simp only [Except.ok.injEq, reduceCtorEq] at h)
  all_goals (subst h; rfl)

/-- Every member of a join has its log recorded wherever the joined log is. -/
theorem LogIn.of_join {ctx : TypeContext} {first : TypeResult} {rest : List TypeResult}
    {joined : TypeResult} {P : TagMeaning}
    (h : LogIn joined.tagLog' P) (hjoin : joinTypeResults ctx first rest = .ok joined) :
    ∀ r ∈ first :: rest, LogIn r.tagLog' P := by
  rw [joinTypeResults_tagLog ctx first rest joined hjoin, ← List.flatMap_cons] at h
  intro r hr a ha
  exact h a (List.mem_flatMap.mpr ⟨r, hr, ha⟩)

/-- A frame for a join is a frame for each of its members. -/
theorem TagFrame.of_join {predSat : PredSat} {tm : TagMeaning} {ctx : TypeContext}
    {first : TypeResult} {rest : List TypeResult} {joined : TypeResult}
    (h : TagFrame predSat tm joined.tagLog') (hjoin : joinTypeResults ctx first rest = .ok joined) :
    ∀ r ∈ first :: rest, TagFrame predSat tm r.tagLog' := by
  rw [joinTypeResults_tagLog ctx first rest joined hjoin, ← List.flatMap_cons] at h
  intro r hr
  exact h.sub fun a ha => List.mem_flatMap.mpr ⟨r, hr, ha⟩

/-- Logs of threaded closure applications: each application allocates from its
    cursor, so the concatenated logs are fresh from the first cursor up to any
    bound on the results' counters. -/
private theorem applyClosuresThreaded_logFresh {α : Type}
    (applyOne : α → Tag × Loc → TypecheckM TypeResult)
    (hOne : ∀ item c r, applyOne item c = .ok r → LogFresh c.1 r.nextTag' r.tagLog' ∧ c.1 ≤ r.nextTag') :
    ∀ (items : List α) (cursor : Tag × Loc) (results : List TypeResult) (hi : Tag),
      applyClosuresThreaded applyOne items cursor = .ok results →
      (∀ r ∈ results, r.nextTag' ≤ hi) →
      LogFresh cursor.1 hi (results.flatMap (·.tagLog')) := by
  intro items
  induction items with
  | nil =>
      intro cursor results hi hthread _
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      subst hthread
      exact LogFresh.nil _ _
  | cons item rest ih =>
      intro cursor results hi hthread hbound
      simp only [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne item cursor with
      | error _ => simp [hfirst] at hthread
      | ok first =>
          simp only [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne rest (first.nextTag', first.nextLoc') with
          | error _ => simp [hrest] at hthread
          | ok restResults =>
              simp only [hrest, pure, Except.pure, Except.ok.injEq] at hthread
              subst hthread
              obtain ⟨hlogFirst, hadv⟩ := hOne item cursor first hfirst
              have hfirstLe : first.nextTag' ≤ hi := hbound first (List.mem_cons_self ..)
              have hrestLog := ih (first.nextTag', first.nextLoc') restResults hi hrest
                (fun r hr => hbound r (List.mem_cons_of_mem _ hr))
              simp only [List.flatMap_cons]
              exact LogFresh.append (LogFresh.mono hlogFirst (Nat.le_refl _) (Nat.le_refl _))
                hrestLog hadv hfirstLe

private theorem tc_mono {ctx : TypeContext} {e : Expr} {fuel : Nat} {res : TypeResult}
    (h : typecheckExpr ctx e fuel = .ok res) : ctx.nextTag ≤ res.nextTag' :=
  typecheck_nextTag_mono ctx e fuel res h

private theorem nil_fresh {lo hi : Tag} {res : TypeResult} (h : res.tagLog' = []) :
    LogFresh lo hi res.tagLog' := by
  rw [h]; exact LogFresh.nil _ _

/-- Two typing runs in sequence: the second starts from the first's counter. -/
private theorem seq_fresh {m : Nat}
    (IH : ∀ ctx e res, typecheckExpr ctx e m = .ok res → LogFresh ctx.nextTag res.nextTag' res.tagLog')
    {c1 c2 : TypeContext} {e1 e2 : Expr} {r1 r2 : TypeResult}
    (h1 : typecheckExpr c1 e1 m = .ok r1) (h2 : typecheckExpr c2 e2 m = .ok r2)
    (hc : c2.nextTag = r1.nextTag') :
    LogFresh c1.nextTag r2.nextTag' (r1.tagLog' ++ r2.tagLog') := by
  have b := IH _ _ _ h2
  rw [hc] at b
  exact LogFresh.append (IH _ _ _ h1) b (tc_mono h1) (hc ▸ tc_mono h2)

/-- Three typing runs in sequence (the conditional); the result counter is the
    maximum of the two arms'. -/
private theorem seq3_fresh {m : Nat}
    (IH : ∀ ctx e res, typecheckExpr ctx e m = .ok res → LogFresh ctx.nextTag res.nextTag' res.tagLog')
    {c1 c2 c3 : TypeContext} {e1 e2 e3 : Expr} {r1 r2 r3 : TypeResult}
    (h1 : typecheckExpr c1 e1 m = .ok r1) (h2 : typecheckExpr c2 e2 m = .ok r2)
    (h3 : typecheckExpr c3 e3 m = .ok r3)
    (hc2 : c2.nextTag = r1.nextTag') (hc3 : c3.nextTag = r2.nextTag') :
    LogFresh c1.nextTag (max r2.nextTag' r3.nextTag') (r1.tagLog' ++ r2.tagLog' ++ r3.tagLog') := by
  have h12 := seq_fresh IH h1 h2 hc2
  have c := IH _ _ _ h3
  rw [hc3] at c
  have m3 := tc_mono h3
  rw [hc3] at m3
  exact LogFresh.mono (LogFresh.append h12 c (Nat.le_trans (tc_mono h1) (hc2 ▸ tc_mono h2)) m3)
    (Nat.le_refl _) (Nat.le_max_right _ _)

private theorem typecheckExternVal_logFresh (ctx : TypeContext) (id : ExternId) (typ : Typ)
    (poison : Bool) (pred : SyntaxPredicate) (fuel : Nat) (res : TypeResult)
    (h : typecheckExternVal ctx id typ poison pred fuel = .ok res) :
    LogFresh ctx.nextTag res.nextTag' res.tagLog' := by
  obtain ⟨_, tagMapping, nextTag', _, _, halloc, _, _, rfl⟩ := typecheckExternVal_ok_shape h
  exact externTagLog_logFresh' [pred] ctx.varEnv ctx.nextTag (tagMapping, nextTag') halloc

/-- Split every `match` in `h` and discharge the error branches. -/
local macro "split_ok" h:ident : tactic => `(tactic| (
  (try simp only [bind, Except.bind, pure, Except.pure] at $h:ident)
  repeat' split at $h:ident
  all_goals (try simp only [pure, Except.pure, MonadExceptOf.throw, throwThe,
    Except.ok.injEq, reduceCtorEq] at $h:ident)
  all_goals (first | (cases $h:ident; done) | skip)))

/-- Every result of a threaded closure application starts at or after the
    first cursor. -/
private theorem applyClosuresThreaded_lb {α : Type}
    (applyOne : α → Tag × Loc → TypecheckM TypeResult)
    (hOne : ∀ item c r, applyOne item c = .ok r → c.1 ≤ r.nextTag') :
    ∀ (items : List α) (cursor : Tag × Loc) (results : List TypeResult),
      applyClosuresThreaded applyOne items cursor = .ok results →
      ∀ r ∈ results, cursor.1 ≤ r.nextTag' := by
  intro items
  induction items with
  | nil =>
      intro cursor results hthread r hr
      simp [applyClosuresThreaded, pure, Except.pure] at hthread
      subst hthread
      cases hr
  | cons item rest ih =>
      intro cursor results hthread r hr
      simp only [applyClosuresThreaded, bind, Except.bind] at hthread
      cases hfirst : applyOne item cursor with
      | error _ => simp [hfirst] at hthread
      | ok first =>
          simp only [hfirst] at hthread
          cases hrest : applyClosuresThreaded applyOne rest (first.nextTag', first.nextLoc') with
          | error _ => simp [hrest] at hthread
          | ok restResults =>
              simp only [hrest, pure, Except.pure, Except.ok.injEq] at hthread
              subst hthread
              have hadv := hOne item cursor first hfirst
              rcases List.mem_cons.mp hr with rfl | hr
              · exact hadv
              · exact Nat.le_trans hadv (ih _ _ hrest r hr)

/-- The joined result's counter bounds every member's. -/
private theorem join_bound (ctx : TypeContext) (first : TypeResult) (rest : List TypeResult)
    (joined : TypeResult) (hjoin : joinTypeResults ctx first rest = .ok joined) :
    ∀ r ∈ first :: rest, r.nextTag' ≤ joined.nextTag' := by
  intro r hr
  rw [joinTypeResults_nextTag_eq_max ctx first rest joined hjoin]
  apply List.le_max_of_mem
  rcases List.mem_cons.mp hr with rfl | hr
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hr)

/-- Application: the argument, then the function, then the threaded closure
    applications, then their join. -/
private theorem app_fresh {α : Type} {m : Nat}
    (IH : ∀ ctx e res, typecheckExpr ctx e m = .ok res → LogFresh ctx.nextTag res.nextTag' res.tagLog')
    {ctx c1 : TypeContext} {e1 e2 : Expr} {r1 r2 : TypeResult}
    (h2 : typecheckExpr ctx e2 m = .ok r2) (h1 : typecheckExpr c1 e1 m = .ok r1)
    (hc : c1.nextTag = r2.nextTag')
    (applyOne : α → Tag × Loc → TypecheckM TypeResult)
    (hOne : ∀ item c r, applyOne item c = .ok r → LogFresh c.1 r.nextTag' r.tagLog' ∧ c.1 ≤ r.nextTag')
    {tcls : List α} {first joined : TypeResult} {rest : List TypeResult} {loc : Loc}
    (hmap : applyClosuresThreaded applyOne tcls (r1.nextTag', loc) = .ok (first :: rest))
    (hjoin : joinTypeResults ctx first rest = .ok joined) :
    LogFresh ctx.nextTag joined.nextTag' (r2.tagLog' ++ (r1.tagLog' ++ joined.tagLog')) := by
  have f12 := seq_fresh IH h2 h1 hc
  have hbound := join_bound ctx first rest joined hjoin
  have hthr := applyClosuresThreaded_logFresh applyOne hOne tcls _ _ joined.nextTag' hmap hbound
  have hlb := applyClosuresThreaded_lb applyOne (fun i c r h => (hOne i c r h).2) tcls _ _ hmap
    first (List.mem_cons_self ..)
  rw [joinTypeResults_tagLog ctx first rest joined hjoin, ← List.flatMap_cons, ← List.append_assoc]
  have m1 := tc_mono h1
  rw [hc] at m1
  exact LogFresh.append f12 hthr (Nat.le_trans (tc_mono h2) m1)
    (Nat.le_trans hlb (hbound first (List.mem_cons_self ..)))

/-- Every typing run allocates fresh tags: each logged tag lies in
    `[ctx.nextTag, res.nextTag')`, and two log entries with the same tag are
    the same allocation. -/
theorem typecheckExpr_tagLog_fresh : ∀ (fuel : Nat) (ctx : TypeContext) (e : Expr) (res : TypeResult),
    typecheckExpr ctx e fuel = .ok res → LogFresh ctx.nextTag res.nextTag' res.tagLog' := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel IH =>
  intro ctx e res h
  cases fuel with
  | zero => simp [typecheckExpr, throw, throwThe, MonadExceptOf.throw] at h
  | succ n =>
  unfold typecheckExpr at h
  cases e with
  | num _ => simp only [typecheckInt, pure, Except.pure, Except.ok.injEq] at h; subst h; exact LogFresh.nil _ _
  | bool _ => simp only [typecheckBool, pure, Except.pure, Except.ok.injEq] at h; subst h; exact LogFresh.nil _ _
  | unit => simp only [typecheckUnit, pure, Except.pure, Except.ok.injEq] at h; subst h; exact LogFresh.nil _ _
  | str _ => simp only [typecheckString, pure, Except.pure, Except.ok.injEq] at h; subst h; exact LogFresh.nil _ _
  | var x => exact nil_fresh (typecheckVar_tagLog _ _ _ h)
  | fn _ _ _ _ => exact nil_fresh (typecheckFn_tagLog _ _ _ _ _ _ h)
  | pfn _ _ _ _ => exact nil_fresh (typecheckPfn_tagLog _ _ _ _ _ _ h)
  | externVal _ _ _ _ => exact typecheckExternVal_logFresh _ _ _ _ _ _ _ h
  | externRef _ _ _ _ _ => exact nil_fresh (typecheckExternRef_tagLog _ _ _ _ _ _ _ h)
  | externFn _ _ _ _ _ _ _ _ => exact nil_fresh (typecheckExternFn_tagLog _ _ _ _ _ _ _ _ _ _ h)
  | externPfn _ _ _ _ _ _ _ => exact nil_fresh (typecheckExternPfn_tagLog _ _ _ _ _ _ _ _ _ h)
  | op e1 op e2 =>
      cases n with
      | zero => simp [typecheckOp, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        unfold typecheckOp at h
        split_ok h
        subst h
        exact seq_fresh IHm ‹typecheckExpr ctx e1 m = .ok _› ‹typecheckExpr _ e2 m = .ok _› rfl
  | newRef e =>
      cases n with
      | zero => simp [typecheckNewRef, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        unfold typecheckNewRef at h
        split_ok h
        all_goals (subst h; have hh := IHm _ _ _ ‹typecheckExpr ctx e m = .ok _›; exact hh)
  | assign e1 e2 =>
      cases n with
      | zero => simp [typecheckAssign, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        unfold typecheckAssign at h
        split_ok h
        all_goals subst h
        all_goals exact seq_fresh IHm ‹typecheckExpr ctx e1 m = .ok _› ‹typecheckExpr _ e2 m = .ok _› rfl
  | deref e =>
      cases n with
      | zero => simp [typecheckDeref, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        unfold typecheckDeref at h
        split_ok h
        all_goals (subst h; have hh := IHm _ _ _ ‹typecheckExpr ctx e m = .ok _›; exact hh)
  | seq e1 e2 =>
      cases n with
      | zero => simp [typecheckSeq, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        unfold typecheckSeq at h
        split_ok h
        subst h
        exact seq_fresh IHm ‹typecheckExpr ctx e1 m = .ok _› ‹typecheckExpr _ e2 m = .ok _› rfl
  | vlet x e1 e2 =>
      cases n with
      | zero => simp [typecheckVlet, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        unfold typecheckVlet at h
        split_ok h
        all_goals (subst h; exact seq_fresh IHm ‹typecheckExpr ctx e1 m = .ok _› ‹typecheckExpr _ e2 m = .ok _› rfl)
  | unaryop op e =>
      cases n with
      | zero => simp [typecheckUnaryOp, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        unfold typecheckUnaryOp at h
        split_ok h
        subst h
        have hh := IHm _ _ _ ‹typecheckExpr ctx e m = .ok _›
        exact hh
  | ite e1 e2 e3 =>
      cases n with
      | zero => simp [typecheckIf, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        unfold typecheckIf at h
        split_ok h
        all_goals (subst h)
        all_goals (
          have h2 := ‹typecheckExpr _ e2 m = .ok _›
          have h3 := ‹typecheckExpr _ e3 m = .ok _›
          first
          | (have h1 := ‹typecheckExpr ctx e1 m = .ok _›
             have hh := seq3_fresh IHm h1 h2 h3 rfl rfl
             exact hh)
          | (have h1 := ‹typecheckExpr { ctx with pureCtx := true } e1 m = .ok _›
             have hh := seq3_fresh IHm h1 h2 h3 rfl rfl
             exact hh))
  | app e1 e2 =>
      cases n with
      | zero => simp [typecheckApp, throw, throwThe, MonadExceptOf.throw] at h
      | succ m =>
        have IHm := IH m (by omega)
        rcases typecheckApp_arrow_structure_full ctx e1 e2 m res h with
          ⟨r2, r1, etyp2, p2, pred2, _hq2, h2, h1, hcases⟩
        rcases hcases with
          ⟨st1, st2, p, p1, tcls, results, first, rest, joined, _, _, _, _, _, hmap, hres, hjoin, rfl⟩ |
          ⟨st1, st2, p, p1, tcls, results, first, rest, joined, _, _, _, _, hmap, hres, hjoin, rfl⟩
        · subst hres
          refine app_fresh IHm h2 h1 rfl _ ?_ hmap hjoin
          intro item c r hr
          refine ⟨?_, applyFnTClosureAtCursor_nextTag_advance _ _ _ _ _ _ _ _ _ _ _ _ _ hr⟩
          cases m with
          | zero => simp [applyFnTClosureAtCursor, throw, throwThe, MonadExceptOf.throw] at hr
          | succ k =>
              exact applyFnTClosureAtCursor_logFresh item st1 st2 p p1 etyp2 p2 pred2 ctx r1 c k r
                (IH k (by omega)) hr
        · subst hres
          refine app_fresh IHm h2 h1 rfl _ ?_ hmap hjoin
          intro item c r hr
          refine ⟨?_, applyPFnTClosureAtCursor_nextTag_advance _ _ _ _ _ _ _ _ _ _ _ _ _ hr⟩
          cases m with
          | zero => simp [applyPFnTClosureAtCursor, throw, throwThe, MonadExceptOf.throw] at hr
          | succ k =>
              exact applyPFnTClosureAtCursor_logFresh item st1 st2 p p1 etyp2 p2 pred2 ctx r1 c k r
                (IH k (by omega)) hr

/-- Every successful typing run allocates fresh tags. -/
theorem typecheck_tagLog_fresh (ctx : TypeContext) (e : Expr) (fuel : Nat) (res : TypeResult)
    (h : typecheck ctx e fuel = .ok res) : LogFresh ctx.nextTag res.nextTag' res.tagLog' :=
  typecheckExpr_tagLog_fresh fuel ctx e res h

/-- The program table of a run contains the starting table and every allocation
    of the run, and adds nothing else. -/
theorem typecheck_programTable (tm : TagMeaning) (ctx : TypeContext) (e : Expr) (fuel : Nat)
    (res : TypeResult) (hbounded : TagMeaningBounded tm ctx.nextTag)
    (h : typecheck ctx e fuel = .ok res) :
    tm ⊑ programTable tm res.tagLog' ∧ LogIn res.tagLog' (programTable tm res.tagLog') ∧
      WithinLog tm res.tagLog' (programTable tm res.tagLog') := by
  have hfresh := typecheck_tagLog_fresh ctx e fuel res h
  exact ⟨programTable_extends tm res.tagLog' ctx.nextTag hbounded (fun a ha => (hfresh.1 a ha).1),
    programTable_logIn tm res.tagLog' hfresh.2, programTable_within tm res.tagLog'⟩

/-- Every table built during a typing run is part of the program table: a table
    that adds to the starting table only allocations of the run is contained in
    it. -/
theorem typecheck_table_sub_programTable {tm tm' : TagMeaning} {ctx : TypeContext} {e : Expr}
    {fuel : Nat} {res : TypeResult} (hbounded : TagMeaningBounded tm ctx.nextTag)
    (h : typecheck ctx e fuel = .ok res) (hwithin : WithinLog tm res.tagLog' tm') :
    tm' ⊑ programTable tm res.tagLog' := by
  obtain ⟨hsub, hlog, _⟩ := typecheck_programTable tm ctx e fuel res hbounded h
  exact WithinLog.submap hwithin hsub hlog

/-! ### Logs of composite rules

Each lemma takes the sub-runs of a rule (as the structure lemmas of
`TypeSafety` expose them) and gives the log of the whole run. -/

/-- Close a rule's log goal: split the remaining matches, discard the error
    branches, and identify the sub-runs with the given ones. -/
local macro "log_close" h:ident : tactic => `(tactic| (
  repeat' split at $h:ident
  all_goals (try simp only [pure, Except.pure, throw, MonadExceptOf.throw, throwThe,
    Except.ok.injEq, reduceCtorEq] at *)
  all_goals (first | (subst $h:ident; first | rfl | simp_all) | skip)))

theorem typecheckUnaryOp_tagLog {ctx : TypeContext} {op : UnaryOp} {e1 : Expr} {fuel : Nat}
    {res r1 : TypeResult} (h : typecheckUnaryOp ctx op e1 fuel = .ok res)
    (h1 : typecheckExpr ctx e1 (fuel - 1) = .ok r1) : res.tagLog' = r1.tagLog' := by
  cases fuel with
  | zero => simp [typecheckUnaryOp, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel] at h1
    unfold typecheckUnaryOp at h
    simp only [bind, Except.bind, h1] at h
    log_close h

theorem typecheckDeref_tagLog {ctx : TypeContext} {e1 : Expr} {fuel : Nat}
    {res r1 : TypeResult} (h : typecheckDeref ctx e1 fuel = .ok res)
    (h1 : typecheckExpr ctx e1 (fuel - 1) = .ok r1) : res.tagLog' = r1.tagLog' := by
  cases fuel with
  | zero => simp [typecheckDeref, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel] at h1
    unfold typecheckDeref at h
    simp only [bind, Except.bind, h1] at h
    log_close h

theorem typecheckNewRef_tagLog {ctx : TypeContext} {e1 : Expr} {fuel : Nat}
    {res r1 : TypeResult} (h : typecheckNewRef ctx e1 fuel = .ok res)
    (h1 : typecheckExpr ctx e1 (fuel - 1) = .ok r1) : res.tagLog' = r1.tagLog' := by
  cases fuel with
  | zero => simp [typecheckNewRef, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel] at h1
    unfold typecheckNewRef at h
    simp only [bind, Except.bind, h1] at h
    log_close h

theorem typecheckOp_tagLog {ctx : TypeContext} {e1 e2 : Expr} {op : Op} {fuel : Nat}
    {res r1 r2 : TypeResult} (h : typecheckOp ctx e1 e2 fuel op = .ok res)
    (h1 : typecheckExpr ctx e1 (fuel - 1) = .ok r1)
    (h2 : typecheckExpr (updateCtxFromResult ctx r1) e2 (fuel - 1) = .ok r2) :
    res.tagLog' = r1.tagLog' ++ r2.tagLog' := by
  cases fuel with
  | zero => simp [typecheckOp, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel, updateCtxFromResult] at h1 h2
    unfold typecheckOp at h
    simp only [bind, Except.bind, h1, h2] at h
    log_close h

theorem typecheckAssign_tagLog {ctx : TypeContext} {e1 e2 : Expr} {fuel : Nat}
    {res r1 r2 : TypeResult} (h : typecheckAssign ctx e1 e2 fuel = .ok res)
    (h1 : typecheckExpr ctx e1 (fuel - 1) = .ok r1)
    (h2 : typecheckExpr (updateCtxFromResult ctx r1) e2 (fuel - 1) = .ok r2) :
    res.tagLog' = r1.tagLog' ++ r2.tagLog' := by
  cases fuel with
  | zero => simp [typecheckAssign, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel, updateCtxFromResult] at h1 h2
    unfold typecheckAssign at h
    simp only [bind, Except.bind, h1, h2] at h
    log_close h

theorem typecheckVlet_tagLog {ctx : TypeContext} {x : Name} {e1 e2 : Expr} {fuel : Nat}
    {res r1 r2 : TypeResult} (h : typecheckVlet ctx x e1 e2 fuel = .ok res)
    (h1 : typecheckExpr ctx e1 (fuel - 1) = .ok r1)
    (h2 : typecheckExpr
      { ctx with
          memEnv := r1.memEnv', varEnv := ctx.varEnv.update x r1.qualType,
          tagEnv := r1.tagEnv', nextLoc := r1.nextLoc', nextTag := r1.nextTag',
          regime := r1.regime', declaredExternRefs := r1.declared' } e2 (fuel - 1) = .ok r2) :
    res.tagLog' = r1.tagLog' ++ r2.tagLog' := by
  cases fuel with
  | zero => simp [typecheckVlet, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel] at h1 h2
    unfold typecheckVlet at h
    simp only [bind, Except.bind, h1, h2] at h
    log_close h

/-- The log of a conditional whose guard has a known regime value: the pure
    typing of the condition, then both arms. -/
theorem typecheckIf_tagLog_matched {ctx : TypeContext} {e1 e2 e3 : Expr} {fuel : Nat}
    {res res1 res2 res3 : TypeResult} {k : Tag} {deps : Deps} {b : Bool}
    (h : typecheckIf ctx e1 e2 e3 fuel = .ok res)
    (hm : matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .ok (k, deps))
    (hk : ctx.regime.lookup? k = some b)
    (h1 : typecheckExpr { ctx with pureCtx := true } e1 (fuel - 1) = .ok res1)
    (h2 : typecheckExpr
      { ctx with
          tagEnv := ctx.tagEnv.insert k ⟨true, deps⟩,
          nextTag := res1.nextTag', declaredExternRefs := res1.declared' } e2 (fuel - 1) = .ok res2)
    (h3 : typecheckExpr
      { ctx with
          tagEnv := ctx.tagEnv.insert k ⟨false, deps⟩,
          nextLoc := res2.nextLoc', nextTag := res2.nextTag',
          declaredExternRefs := res2.declared' } e3 (fuel - 1) = .ok res3) :
    res.tagLog' = res1.tagLog' ++ res2.tagLog' ++ res3.tagLog' := by
  cases fuel with
  | zero => simp [typecheckIf, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel] at hm h1 h2 h3
    unfold typecheckIf at h
    simp only [bind, Except.bind, hm, h1, hk] at h
    cases b <;> simp only [h2, h3] at h <;> log_close h

/-- The log of a conditional typed by the standard rule: the condition, then
    both arms.  (In the unknown-regime case the gate typing of the condition is
    not part of the run.) -/
theorem typecheckIf_tagLog_std {ctx : TypeContext} {e1 e2 e3 : Expr} {fuel : Nat}
    {res res1 res2 res3 : TypeResult}
    (h : typecheckIf ctx e1 e2 e3 fuel = .ok res)
    (hstd : (∃ (k : Tag) (deps : Deps),
        matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .ok (k, deps) ∧
        ctx.regime.lookup? k = none) ∨
      (∃ err, matchGuard e1 ctx.memEnv ctx.varEnv (fuel - 1) = .error err))
    (h1 : typecheckExpr ctx e1 (fuel - 1) = .ok res1)
    (h2 : typecheckExpr
      { ctx with
          memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res1.nextLoc',
          nextTag := res1.nextTag', regime := res1.regime', declaredExternRefs := res1.declared',
          pc := joinPoison ctx.pc res1.qualType.poison } e2 (fuel - 1) = .ok res2)
    (h3 : typecheckExpr
      { ctx with
          memEnv := res1.memEnv', tagEnv := res1.tagEnv', nextLoc := res2.nextLoc',
          nextTag := res2.nextTag', regime := res1.regime', declaredExternRefs := res2.declared',
          pc := joinPoison ctx.pc res1.qualType.poison } e3 (fuel - 1) = .ok res3) :
    res.tagLog' = res1.tagLog' ++ res2.tagLog' ++ res3.tagLog' := by
  cases fuel with
  | zero => simp [typecheckIf, throw, throwThe, MonadExceptOf.throw] at h
  | succ m =>
    simp only [Nat.add_sub_cancel] at hstd h1 h2 h3
    unfold typecheckIf at h
    rcases hstd with ⟨k, deps, hm, hk⟩ | ⟨err, hm⟩
    · simp only [bind, Except.bind, hm, hk, h1] at h
      log_close h
    · simp only [bind, Except.bind, hm, h1] at h
      log_close h
