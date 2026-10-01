import Solcore.SourceSemantics.CoreLowering.CallablePairedProtocol

/-! Static receipts from the actual paired compiler hooks. These identify the
emitted native helper and descriptor lookup; finite protocol lemmas carry the
separate dynamic metadata history. Neither layer infers history from a Word. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedEmission
open Core Frontend SourceInference
open SourceCoreCallablePairedAncestry

private theorem key_eq_of_beq (left right : Key) (accepted : (left == right) = true) : left = right := by
  cases left
  cases right
  delta SourceSpecialization.instBEqSpecializationKey SourceSpecialization.instBEqSpecializationKey.beq at accepted
  simp only [Bool.and_eq_true, beq_iff_eq] at accepted
  simp_all

private theorem type_beq (left right : Core.Ty) : (left == right) = true ↔ left = right := by
  induction left generalizing right <;> cases right <;>
    simp_all [BEq.beq, Core.instBEqTy.beq, Core.instBEqDataTypeId.beq]
  rename_i left right
  cases left; cases right; simp_all

/-- The hook's selected word belongs to its actual base callable table. -/
theorem originId_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {origin : SourceCoreStageCodebook.Origin} {id : Word}
    (accepted : originId prepared origin = .ok id) :
    ∃ native, base.callableContext = some native ∧ native.table.idAt? origin = some id := by
  unfold originId at accepted
  split at accepted
  · next native selected =>
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    · next actual found =>
      cases accepted
      exact ⟨native, selected, found⟩
    · cases accepted
  · cases accepted

/-- A successful actual lambda expression hook emits this exact snapshot
helper with the source occurrence's owned descriptor. Header checks and source
owner checks are retained independently of any runtime closure value. -/
theorem expressionHook_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output) :
    ∃ native origin body, base.callableContext = some native ∧
      native.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      context.owner = owner ∧ context.globals = base.globals ∧ source.owner = owner.declaration ∧
      output = snapshotLambda prepared.layout.frame origin (creationReferenceIndex context scope) parameter result body := by
  by_cases globals : (context.owner != owner || context.globals != base.globals) = true
  · simp [expressionHook, globals, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  · have checkedGlobals : (context.owner == owner) = true ∧ context.globals = base.globals := by
      simpa [bne] using globals
    have globalsEq : context.owner = owner ∧ context.globals = base.globals :=
      ⟨key_eq_of_beq _ _ checkedGlobals.1, checkedGlobals.2⟩
    cases originSelected : originId prepared (.lambda owner node.id active) with
    | error error => simp [expressionHook, globals, originSelected, bind, Except.bind] at accepted
    | ok origin =>
      obtain ⟨native, nativeSelected, selected⟩ := originId_receipt prepared originSelected
      cases raw <;> simp only [expressionHook, globals, originSelected, pure, Except.pure, bind, Except.bind] at accepted
      all_goals try cases accepted
      next actualParameter actualResult body =>
        by_cases header : (actualParameter != parameter || actualResult != LanguageResult.resultType result) = true
        · simp [header, throw, throwThe, MonadExceptOf.throw] at accepted
        · have headerChecks : (actualParameter == parameter) = true ∧ (actualResult == LanguageResult.resultType result) = true := by
            simpa [bne] using header
          have headerEq := And.intro ((type_beq _ _).mp headerChecks.1) ((type_beq _ _).mp headerChecks.2)
          by_cases ownerEq : (source.owner != owner.declaration) = true
          · simp [header, ownerEq, throw, throwThe, MonadExceptOf.throw] at accepted
          · have sourceOwner : source.owner = owner.declaration := by simpa using ownerEq
            simp [header, ownerEq] at accepted
            exact ⟨native, origin, body, nativeSelected, selected, by simp only [headerEq.1, headerEq.2],
              globalsEq.1, globalsEq.2, sourceOwner, accepted.symm⟩

theorem namedBody_receipt {checked : Checked} {base : Base checked} (prepared : Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : namedBody prepared function body = .ok output) :
    ∃ native origin, base.callableContext = some native ∧
      native.table.idAt? (.named function.signature.key) = some origin ∧
      output = SourceCoreCallablePairedFrames.withFrame (.var (base.globals.length + 1))
        (SourceCoreCallablePairedFrames.named prepared.layout.frame origin) body := by
  unfold namedBody at accepted
  obtain ⟨origin, selected, accepted⟩ := CallableAncestryPairedExpansion.bind_ok accepted
  cases accepted
  obtain ⟨native, nativeSelected, originSelected⟩ := originId_receipt prepared selected
  exact ⟨native, origin, nativeSelected, originSelected, rfl⟩


/-- A real successful expression hook creates exactly a closure retaining the
current authenticated source metadata and the original lexical environment. -/
theorem expressionHook_history {checked : Checked} {base : Base checked}
    (prepared : Prepared base) {inputs : CallableAncestryPairedLookup.Inputs base}
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output)
    {environment : Environment} {store : Store} {location : Location}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State}
    (reference : environment[creationReferenceIndex context scope]? = some (.cellRef prepared.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallablePairedFrames.encode prepared.layout.frame frame))
    (history : CallableAncestryPairedLookup.Authenticates inputs frame (some state)) :
    ∃ native origin body value, base.callableContext = some native ∧
      native.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      Evaluates environment store output value store ∧
      CallablePairedProtocol.LambdaSnapshot inputs prepared.layout.frame origin (creationReferenceIndex context scope)
        parameter result body environment value := by
  obtain ⟨native, origin, body, nativeSelected, originSelected, rawShape, _, _, _, rfl⟩ := expressionHook_receipt prepared accepted
  obtain ⟨value, evaluated, snapshot⟩ := CallablePairedProtocol.snapshotLambda_history reference read history
  exact ⟨native, origin, body, value, nativeSelected, originSelected, rawShape, evaluated, snapshot⟩

/-- Every completed execution of this emitted formation helper keeps precisely
the same saved frame and capture order, with no new heap effects. -/
theorem expressionHook_reflects {checked : Checked} {base : Base checked}
    (prepared : Prepared base) {inputs : CallableAncestryPairedLookup.Inputs base}
    {owner : Key} {active : Active} {context : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : Scope} {node : ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : expressionHook prepared owner active context source scope node parameter result raw = .ok output)
    {environment : Environment} {before after : Store} {location : Location} {value : Value}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State}
    (reference : environment[creationReferenceIndex context scope]? = some (.cellRef prepared.layout.frame.type location))
    (read : before.read? location = some (SourceCoreCallablePairedFrames.encode prepared.layout.frame frame))
    (history : CallableAncestryPairedLookup.Authenticates inputs frame (some state))
    (evaluated : Evaluates environment before output value after) :
    after = before ∧ ∃ native origin body, base.callableContext = some native ∧
      native.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      CallablePairedProtocol.LambdaSnapshot inputs prepared.layout.frame origin (creationReferenceIndex context scope)
        parameter result body environment value := by
  obtain ⟨native, origin, body, expected, nativeSelected, originSelected, rawShape, expectedEval, snapshot⟩ :=
    expressionHook_history prepared accepted reference read history
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated expectedEval
  exact ⟨rfl, native, origin, body, nativeSelected, originSelected, rawShape, snapshot⟩

/-- The actual named-body hook selects a successful named metadata seed from
the codebook generated by the same compatible compiler. -/
theorem namedBody_enters {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat} {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (prepared : Prepared base) (inputs : CallableAncestryPairedLookup.Inputs base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : namedBody prepared function body = .ok output) :
    ∃ origin state, SourceCoreCallableAncestryPairedPreparation.named? inputs origin = some state ∧
      output = SourceCoreCallablePairedFrames.withFrame (.var (base.globals.length + 1))
        (SourceCoreCallablePairedFrames.named prepared.layout.frame origin) body := by
  obtain ⟨native, origin, nativeSelected, originSelected, emitted⟩ := namedBody_receipt prepared accepted
  have nativeSame := Option.some.inj (nativeSelected.symm.trans inputs.callableSelected)
  subst native
  unfold SourceCoreStageCodebook.Table.idAt? at originSelected
  cases found : inputs.callable.table.entries.find? (fun entry => decide (entry.origin = .named function.signature.key)) with
  | none => simp only [found, Option.map_none] at originSelected; cases originSelected
  | some entry =>
    have namedOrigin : entry.origin = .named function.signature.key := by simpa using List.find?_some found
    have identifier : entry.id = origin := by simpa only [found, Option.map_some, Option.some.injEq] using originSelected
    obtain ⟨state, generated⟩ := CallableAncestryPairedSeeds.named_total
      (CallableAncestryPairedSeeds.factory_authenticated compiled inputs) (List.mem_of_find?_eq_some found) namedOrigin
    exact ⟨origin, state, identifier ▸ generated, emitted⟩

end Solcore.SourceSemantics.CoreLowering.CallablePairedEmission

