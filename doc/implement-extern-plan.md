<!-- be6267be-e482-4a23-873f-d613f32db49f 1ff6fdb3-a092-451b-8b3f-dbab3f2cfbf7 -->
# Implement extern functions

## Phase 1: Syntax layer (Syntax.lean)

### 1.1 Add syntax-level extern specifications ✅ COMPLETED

Create structures for extern specifications at the syntax level, before typechecking:

```lean
-- Syntax-level predicate (simplified, no captured environment)
-- Parser creates these, typechecker converts to full Predicate
inductive SyntaxPredicate where
  | guardClosure : Tag → Name → Expr → SyntaxPredicate  -- tag, arg name, predicate body (as Expr)
  | guardOnly : Tag → SyntaxPredicate
  | noPred : SyntaxPredicate

-- Effect target: either a named variable or the return value
inductive EffectTarget where
  | namedVar : Name → EffectTarget      -- !varname
  | returnValue : EffectTarget           -- return (special keyword, no ! prefix)

-- Effect specification for impure externs
structure Effect where
  target : EffectTarget
  poison : Bool  -- true for "poisoned", false for "clean"
  pred : SyntaxPredicate

-- Return specification for extern functions (simple or nested)
-- Nested variants allow currying: outer extern returns inner extern
inductive ExternReturn where
  | simple : Typ → Bool → SyntaxPredicate → ExternReturn
  | nestedFn : Name → Typ → ExternReturn → List Effect → ExternReturn
  | nestedPfn : Name → Typ → ExternReturn → ExternReturn
```

Note: Parser assigns unique Tag values to guard placeholders. SyntaxPredicate is converted to Predicate during typechecking (with environment capture).

### 1.2 Add Expr constructors ✅ COMPLETED

Add three new expression constructors to `Expr` inductive type (around line 79):

```lean
| externVal : Typ → Bool → SyntaxPredicate → Expr
| externFn : Name → Typ → ExternReturn → List Effect → Expr
| externPfn : Name → Typ → ExternReturn → Expr
```

### 1.3 Add BEq instances 🔄 IN PROGRESS (termination issue)

Add BEq functions in the mutual block with `beqExpr`:

- `beqSyntaxPredicate` (calls `beqExpr` for the body)
- `beqEffect` (calls `beqSyntaxPredicate`)
- `beqEffectList` (structural recursion on lists)
- `beqExternReturn` (recursive for nested cases, calls `beqSyntaxPredicate` and `beqEffectList`)

**IMPORTANT:** NO PARTIAL DEFINITIONS. Must prove termination using `termination_by` or other tactics.

Extend `beqExpr` function (around line 112) to handle the new constructors:

- Pattern match on `externVal`, `externFn`, and `externPfn`
- Call the helper beq functions

Add instances after the mutual block.

### 1.4 Update Repr instances ✅ COMPLETED

Add Repr functions in the mutual block with `reprExpr`:

- `reprSyntaxPredicate` (avoids showing full body)
- `reprEffect`
- `reprExternReturn` (recursive for nested cases)

Extend `reprExpr` function to display extern expressions concisely.

Add instances after the mutual block.

## Phase 2: BigStep interpreter (BigStep.lean)

### 2.1 Add error cases

In the `beval` function (around line 48), add cases after existing Expr matches (around line 290):

```lean
| Expr.externVal _ _ _ =>
  return .runtimeError "Cannot execute extern value – no implementation provided"
| Expr.externFn _ _ _ _ =>
  return .runtimeError "Cannot execute extern function – no implementation provided"
| Expr.externPfn _ _ _ =>
  return .runtimeError "Cannot execute extern pure function – no implementation provided"
```

## Phase 3: Poison/typing layer (Syntax.lean)

### 3.1 Extend closure types with extern constructors

Modify existing `FnTClosure` and `PFnTClosure` types (around line 311-315) to rename `mk` to `regular` and add `extern` variants:

```lean
-- Typing closure for impure functions
inductive FnTClosure : Type where
  | regular : Name → Expr → List (Name × QTyp) → FnTClosure
  | extern : Name → ExternReturn → List Effect → List (Name × QTyp) → FnTClosure

-- Typing closure for pure functions
inductive PFnTClosure : Type where
  | regular : Name → PExpr → List (Name × QTyp) → PFnTClosure
  | extern : Name → ExternReturn → List (Name × QTyp) → PFnTClosure
```

Note: `ETyp.arrow` and `ETyp.parrow` remain unchanged - they already carry these closure types.

### 3.2 Update all references to FnTClosure.mk and PFnTClosure.mk

Throughout the codebase, update:

- `FnTClosure.mk` → `FnTClosure.regular`
- `PFnTClosure.mk` → `PFnTClosure.regular`

This affects:

- `typecheckFn` (around line 522): `FnTClosure.regular x body ctx.varEnv`
- `typecheckPfn` (around line 536): `PFnTClosure.regular x pbody ctx.varEnv`
- `typecheckApp` pattern matches (around line 959 and 987)

### 3.3 Update BEq and Repr instances

Update the mutual BEq block (around line 458-464):

- Extend `beqFnTClosure` to handle both `regular` and `extern` constructors
- Extend `beqPFnTClosure` to handle both `regular` and `extern` constructors

Update the mutual Repr block (around line 373-377):

- Extend `reprFnTClosure` to handle both `regular` and `extern` constructors
- Extend `reprPFnTClosure` to handle both `regular` and `extern` constructors

No changes needed to `beqETyp`, `reprETyp`, or `beqETypSignature` since `ETyp` is unchanged.

## Phase 4: Typechecker (Typecheck.lean)

### 4.1 Helper: Convert SyntaxPredicate to Predicate and surface types to QTyp

Add before `typecheckExpr` (around line 550):

```lean
-- Convert SyntaxPredicate to Predicate with late environment capture
-- Parser creates SyntaxPredicate with Expr bodies and no captured env
-- Typechecker converts Expr to PExpr and attaches current varEnv
def attachVarEnvToPredicate (pred : SyntaxPredicate) (varEnv : VarTypeEnv) : TypecheckM Predicate :=
  match pred with
  | SyntaxPredicate.guardClosure k arg body =>
      -- Convert body from Expr to PExpr
      let pbody ← body.toPExpr
      return Predicate.guardClosure k arg pbody varEnv
  | SyntaxPredicate.guardOnly k => return Predicate.guardOnly k
  | SyntaxPredicate.noPred => return Predicate.noPred

-- Convert (Typ, Bool, SyntaxPredicate) to QTyp for EXTERN VALUES
--
-- Used only for extern val declarations at definition time.
-- May allocate fresh locations for reference types and update Γ.
--
def surfaceSpecToQTyp (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) 
    (varEnv : VarTypeEnv) (ctx : TypeContext) : TypecheckM (QTyp × TypeContext) := do
  -- Convert Typ to ETyp, allocating locations for references
  let (etyp, ctx') ← match typ with
    | Typ.int => return (ETyp.int, ctx)
    | Typ.bool => return (ETyp.bool, ctx)
    | Typ.unit => return (ETyp.unit, ctx)
    | Typ.string => return (ETyp.string, ctx)
    | Typ.ref t => 
        let (l, ctx') := freshTLoc ctx
        let (innerQt, ctx'') ← surfaceSpecToQTyp t false SyntaxPredicate.noPred varEnv ctx'
        return (ETyp.ref innerQt.etyp l, ctx'')
    | Typ.arrow _ _ => throw "Arrow types not expected in extern specs"
  
  let pred' ← attachVarEnvToPredicate pred varEnv
  return (⟨etyp, poison, pred'⟩, ctx')

-- Convert (Bool, SyntaxPredicate) to QTyp for EFFECT SPECIFICATIONS
--
-- Used when processing effects during extern function application.
-- IMPORTANT: Memory currently stores only integers, so type is always int.
-- Effects specify the type stored AT a memory location (the contents type).
--
def effectSpecToQTyp (poison : Bool) (pred : SyntaxPredicate) 
    (varEnv : VarTypeEnv) : TypecheckM QTyp := do
  let pred' ← attachVarEnvToPredicate pred varEnv
  return ⟨ETyp.int, poison, pred'⟩

-- Convert (Typ, Bool, SyntaxPredicate) to QTyp for RETURN SPECIFICATIONS
--
-- Used when processing return specs during extern function application.
-- May allocate fresh locations for reference types, but does NOT update Γ.
-- The poison/predicate apply to the reference itself, not to the memory location.
--
def returnSpecToQTyp (typ : Typ) (poison : Bool) (pred : SyntaxPredicate)
    (varEnv : VarTypeEnv) (nextLoc : Address) : TypecheckM (QTyp × Address) := do
  -- Convert Typ to ETyp, allocating locations for references
  let (etyp, nextLoc') ← match typ with
    | Typ.int => return (ETyp.int, nextLoc)
    | Typ.bool => return (ETyp.bool, nextLoc)
    | Typ.unit => return (ETyp.unit, nextLoc)
    | Typ.string => return (ETyp.string, nextLoc)
    | Typ.ref t => 
        let l := nextLoc
        let nextLoc' := nextLoc + 1
        let (innerQt, nextLoc'') ← returnSpecToQTyp t false SyntaxPredicate.noPred varEnv nextLoc'
        return (ETyp.ref innerQt.etyp l, nextLoc'')
    | Typ.arrow _ _ => throw "Arrow types not expected in extern specs"
  
  let pred' ← attachVarEnvToPredicate pred varEnv
  return (⟨etyp, poison, pred'⟩, nextLoc')
```

### 4.2 Typecheck extern value

Add `typecheckExternVal` function (around line 580):

```lean
def typecheckExternVal (ctx : TypeContext) (typ : Typ) (poison : Bool) (pred : SyntaxPredicate) 
    : TypecheckM TypeResult := do
  -- Convert to QTyp with current varEnv
  let (qt, ctx') ← surfaceSpecToQTyp typ poison pred ctx.varEnv ctx
  
  -- Return the qualified type
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv, 
           nextLoc' := ctx'.nextLoc, nextTag' := ctx.nextTag }
```

### 4.3 Typecheck extern functions

Add functions (around line 590):

```lean
def typecheckExternFn (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) (effects : List Effect) : TypecheckM TypeResult := do
  -- Create extern closure with captured varEnv
  let tcl := FnTClosure.extern arg retSpec effects ctx.varEnv
  
  -- Create arrow type with ambient pc using existing ETyp.arrow
  let arrowTyp := ETyp.arrow argTyp Typ.unit ctx.pc tcl  -- placeholder for st2
  
  -- Return qualified type with poison = pc
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }

def typecheckExternPfn (ctx : TypeContext) (arg : Name) (argTyp : Typ)
    (retSpec : ExternReturn) : TypecheckM TypeResult := do
  -- Create extern closure with captured varEnv
  let tcl := PFnTClosure.extern arg retSpec ctx.varEnv
  
  -- Create arrow type with ambient pc
  let arrowTyp := ETyp.parrow argTyp Typ.unit ctx.pc tcl
  
  -- Return qualified type with poison = pc
  let qt : QTyp := ⟨arrowTyp, ctx.pc, Predicate.noPred⟩
  return { qualType := qt, memEnv' := ctx.memEnv, tagEnv' := ctx.tagEnv,
           nextLoc' := ctx.nextLoc, nextTag' := ctx.nextTag }
```

### 4.4 Extend typecheckApp for externs

In `typecheckApp` function (around line 937), modify existing `ETyp.arrow` and `ETyp.parrow` cases to handle both `regular` and `extern` closures:

```lean
| ETyp.arrow st1 st2 p tcl =>
  -- Check pure context restriction
  if ctx.pureCtx then
    throw "Pure context disallows application of impure function"
  
  -- Typecheck argument
  let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', 
                nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
  let result2 ← typecheckExpr ctx' e2 fuel
  let argQt := result2.qualType
  
  -- Check subtyping
  if not (isSubtype st1 argQt) then 
    throw s!"Type mismatch in function application: ..."
  
  -- Handle both regular and extern closures
  match tcl with
  | FnTClosure.regular x body capturedEnv =>
      -- Existing regular function application logic (unchanged)
      let argQt' := ⟨argQt.etyp, joinPoison ctx.pc argQt.poison, argQt.pred⟩
      let env' := VarTypeEnv.update capturedEnv x argQt'
      let ctx'' := { ctx with pc := joinPoison p (joinPoison ctx.pc p1), 
                     memEnv := result2.memEnv', varEnv := env', tagEnv := result2.tagEnv',
                     nextTag := result2.nextTag', nextLoc := result2.nextLoc' }
      let result3 ← typecheckExpr ctx'' body fuel
      let ⟨etyp3, p3, pred3⟩ := result3.qualType
      
      if not (isSubtype st2 result3.qualType) then
        throw s!"Type mismatch in function application: ..."
      
      let poison := joinPoison ctx.pc p3
      let qt : QTyp := ⟨etyp3, poison, pred3⟩
      return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv',
               nextLoc' := result3.nextLoc', nextTag' := result3.nextTag' }
  
  | FnTClosure.extern x retSpec effects capturedEnv =>
      -- Extern function application logic
      -- 1. Build unified environment
      let argQt' := ⟨argQt.etyp, joinPoison ctx.pc argQt.poison, argQt.pred⟩
      let unifiedEnv := VarTypeEnv.update capturedEnv x argQt'
      
      -- 2. Process effects
      let mut memEnv := result2.memEnv'
      let mut nextLoc := result2.nextLoc'
      for effect in effects do
        match effect.target with
        | EffectTarget.namedVar v =>
            -- Resolve v in unifiedEnv to get ref location
            match unifiedEnv.lookup v with
            | some qt =>
                match qt.etyp with
                | ETyp.ref _t l =>
                    -- Convert effect spec to QTyp and update Γ(l)
                    let effectQt ← effectSpecToQTyp effect.poison effect.pred unifiedEnv
                    let storedQt := ⟨effectQt.etyp, joinPoison ctx.pc effectQt.poison, effectQt.pred⟩
                    memEnv := memEnv.insert l storedQt
                | _ => throw s!"Effect target {v} must be a reference type"
            | none => throw s!"Effect target {v} not found in environment"
        | EffectTarget.returnValue =>
            -- Will be handled when processing return spec if it's a ref type
            pure ()
      
      -- 3. Handle return spec (simple or nested)
      match retSpec with
      | ExternReturn.simple typ poison pred =>
          -- Simple return type
          let (retQt, nextLoc') ← returnSpecToQTyp typ poison pred unifiedEnv nextLoc
          
          -- If return type is ref and there's a "return" effect, update Γ at that location
          match retQt.etyp with
          | ETyp.ref _t l =>
              -- Check for "return" effect
              let returnEffect := effects.find? (fun eff =>
                match eff.target with
                | EffectTarget.returnValue => true
                | _ => false)
              match returnEffect with
              | some eff =>
                  let effectQt ← effectSpecToQTyp eff.poison eff.pred unifiedEnv
                  let storedQt := ⟨effectQt.etyp, joinPoison ctx.pc effectQt.poison, effectQt.pred⟩
                  memEnv := memEnv.insert l storedQt
              | none => pure ()
          | _ =>
              -- Non-ref return: verify no "return" effect exists
              let hasReturnEffect := effects.any (fun eff =>
                match eff.target with
                | EffectTarget.returnValue => true
                | _ => false)
              if hasReturnEffect then
                throw "Effect on 'return' is only valid when return type is a reference"
          
          let poison' := joinPoison ctx.pc retQt.poison
          let qt := ⟨retQt.etyp, poison', retQt.pred⟩
          return { qualType := qt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                   nextLoc' := nextLoc', nextTag' := result2.nextTag' }
      
      | ExternReturn.nestedFn innerArg innerArgTyp innerRet innerEffects =>
          -- Nested extern function: return a closure
          let innerTcl := FnTClosure.extern innerArg innerRet innerEffects unifiedEnv
          let innerArrowTyp := ETyp.arrow innerArgTyp Typ.unit ctx.pc innerTcl
          let qt := ⟨innerArrowTyp, ctx.pc, Predicate.noPred⟩
          return { qualType := qt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                   nextLoc' := nextLoc, nextTag' := result2.nextTag' }
      
      | ExternReturn.nestedPfn innerArg innerArgTyp innerRet =>
          -- Nested extern pure function: return a closure
          let innerTcl := PFnTClosure.extern innerArg innerRet unifiedEnv
          let innerArrowTyp := ETyp.parrow innerArgTyp Typ.unit ctx.pc innerTcl
          let qt := ⟨innerArrowTyp, ctx.pc, Predicate.noPred⟩
          return { qualType := qt, memEnv' := memEnv, tagEnv' := result2.tagEnv',
                   nextLoc' := nextLoc, nextTag' := result2.nextTag' }

| ETyp.parrow st1 st2 p tcl =>
  -- Typecheck argument
  let ctx' := { ctx with memEnv := result1.memEnv', tagEnv := result1.tagEnv', 
                nextLoc := result1.nextLoc', nextTag := result1.nextTag' }
  let result2 ← typecheckExpr ctx' e2 fuel
  let argQt := result2.qualType
  
  -- Check subtyping
  if not (isSubtype st1 argQt) then 
    throw s!"Type mismatch in function application: ..."
  
  match tcl with
  | PFnTClosure.regular x body capturedEnv =>
      -- Existing regular pure function application logic (unchanged)
      let argQt' := ⟨argQt.etyp, joinPoison ctx.pc argQt.poison, argQt.pred⟩
      let env' := VarTypeEnv.update capturedEnv x argQt'
      let ctx'' := { ctx with memEnv := result2.memEnv', pc := joinPoison p (joinPoison ctx.pc p1),
                     varEnv := env', tagEnv := result2.tagEnv', pureCtx := true,
                     nextLoc := result2.nextLoc', nextTag := result2.nextTag' }
      let result3 ← typecheckExpr ctx'' (PExpr.toExpr body) fuel
      let ⟨etyp3, p3, pred3⟩ := result3.qualType
      
      if not (isSubtype st2 result3.qualType) then
        throw s!"Type mismatch in function application: ..."
      
      let poison := joinPoison ctx.pc p3
      let qt : QTyp := ⟨etyp3, poison, pred3⟩
      return { qualType := qt, memEnv' := result3.memEnv', tagEnv' := result3.tagEnv',
               nextLoc' := result3.nextLoc', nextTag' := result3.nextTag' }
  
  | PFnTClosure.extern x retSpec capturedEnv =>
      -- Extern pure function application (no effects)
      let argQt' := ⟨argQt.etyp, joinPoison ctx.pc argQt.poison, argQt.pred⟩
      let unifiedEnv := VarTypeEnv.update capturedEnv x argQt'
      
      let mut nextLoc := result2.nextLoc'
      
      match retSpec with
      | ExternReturn.simple typ poison pred =>
          let (retQt, nextLoc') ← returnSpecToQTyp typ poison pred unifiedEnv nextLoc
          let poison' := joinPoison ctx.pc retQt.poison
          let qt := ⟨retQt.etyp, poison', retQt.pred⟩
          return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                   nextLoc' := nextLoc', nextTag' := result2.nextTag' }
      
      | ExternReturn.nestedFn innerArg innerArgTyp innerRet innerEffects =>
          -- Nested extern impure function: return a closure
          let innerTcl := FnTClosure.extern innerArg innerRet innerEffects unifiedEnv
          let innerArrowTyp := ETyp.arrow innerArgTyp Typ.unit ctx.pc innerTcl
          let qt := ⟨innerArrowTyp, ctx.pc, Predicate.noPred⟩
          return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                   nextLoc' := nextLoc, nextTag' := result2.nextTag' }
      
      | ExternReturn.nestedPfn innerArg innerArgTyp innerRet =>
          -- Nested extern pure function: return a closure
          let innerTcl := PFnTClosure.extern innerArg innerRet unifiedEnv
          let innerArrowTyp := ETyp.parrow innerArgTyp Typ.unit ctx.pc innerTcl
          let qt := ⟨innerArrowTyp, ctx.pc, Predicate.noPred⟩
          return { qualType := qt, memEnv' := result2.memEnv', tagEnv' := result2.tagEnv',
                   nextLoc' := nextLoc, nextTag' := result2.nextTag' }
```

### 4.5 Update typecheckExpr dispatch

In `typecheckExpr` function (around line 672), add cases:

```lean
| Expr.externVal typ poison pred => typecheckExternVal ctx typ poison pred
| Expr.externFn arg argTyp retSpec effects => 
    typecheckExternFn ctx arg argTyp retSpec effects
| Expr.externPfn arg argTyp retSpec => 
    typecheckExternPfn ctx arg argTyp retSpec
```

## Phase 5: Proof updates (LeanProofs/*.lean)

### 5.1 Equality.lean

Add BEq soundness and reflexivity proofs for new types:

- `SyntaxPredicate`, `EffectTarget`, `Effect`, `ExternReturn` (inductive proofs for recursive structures)
- Extend `FnTClosure` and `PFnTClosure` soundness proofs with new `regular` and `extern` constructors
- Extend `Expr` soundness proof with `externVal`, `externFn`, `externPfn` constructors

Note: No changes needed for `ETyp` proofs since we're not modifying it.

### 5.2 Progress.lean

Add lemma stubs for extern expressions (around line 100):

```lean
lemma progress_externVal : ... := sorry
lemma progress_externFn : ... := sorry
lemma progress_externPfn : ... := sorry
```

Note: These will remain `sorry` as externs are non-executable.

### 5.3 Preservation.lean

Add lemma stubs for extern expressions (around line 100):

```lean
lemma preservation_externVal : ... := sorry
lemma preservation_externFn : ... := sorry
lemma preservation_externPfn : ... := sorry
```

Note: These will remain `sorry` as externs are non-executable.

### 5.4 Properties.lean

No changes needed (externs don't affect existing property proofs).

### 5.5 NonInterference.lean and NonInterferenceProofs.lean

No changes needed initially (externs are placeholders without observable effects at runtime).

## Implementation order

1. Phase 1: Syntax structures and Expr constructors
2. Phase 2: BigStep error handling
3. Phase 3: Extend closure types, rename mk to regular (no ETyp changes)
4. Phase 4: Typechecker implementation
5. Phase 5: Update all proofs

### To-dos

- [ ] Add Effect (without Typ) and ExternReturn (with nestedFn/nestedPfn variants) to Syntax.lean
- [ ] Add Expr.externVal, Expr.externFn, and Expr.externPfn constructors to Syntax.lean
- [ ] Add BEq/Repr for Effect and ExternReturn (recursive), update beqExpr/reprExpr for new constructors
- [ ] Add runtime error cases for extern expressions in BigStep.lean
- [ ] Add extern constructors to FnTClosure and PFnTClosure (no ETyp changes needed)
- [ ] Update beqFnTClosure, beqPFnTClosure, reprFnTClosure, reprPFnTClosure for new constructors
- [ ] Implement tag remapping helpers (remapPredicate, collectExternPlaceholderTags, allocatePlaceholderTags, remapExternReturn) in Typecheck.lean
- [ ] Implement surfaceSpecToQTyp conversion helper
- [ ] Implement typecheckExternVal function
- [ ] Implement typecheckExternFn and typecheckExternPfn functions
- [ ] Extend typecheckApp arrow/parrow cases to handle FnTClosure.extern and PFnTClosure.extern with effect resolution
- [ ] Update typecheckExpr to dispatch to extern typechecking functions
- [ ] Update Equality.lean with BEq proofs for new types and FnTClosure/PFnTClosure/Expr extensions
- [ ] Add sorry lemmas for extern expressions in Progress.lean
- [ ] Add sorry lemmas for extern expressions in Preservation.lean
- [ ] Implement parser support for extern val, extern fn, extern pfn with all syntax elements
- [ ] Create unit test files for extern functionality (extern-basic, extern-effects, extern-nested, etc.)