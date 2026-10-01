import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBuiltinBodyTree
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCallableLambdaViewBuiltinBodyTree
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableLambdaViewEdits CallableLambdaBodyReachability
abbrev Scope := SourceCoreLocalCell.Scope

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source view : TypedSource} {changed : List ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

/-- The compiler really accepts the view body. The recovered canonical Tree
has the exact finished code, but canonical typing, syntax and acceptance are
not conclusions. No static child transformation premise remains. -/
theorem contextual_original
    {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {compilation : SourceCoreFunctions.Context}
    {native : SourceCoreGeneralFunctions.CallableContext} {parent : Option SourceCoreLocalEvidence.Prepared}
    {skipInitializer : Option ExpressionId} {fuel : Nat} {scope : Scope} {context : SourceSemantics.Context}
    (edited : LocalView source view changed)
    (ordinary : CompatibleExpressionBuiltins.Ordinary view locals compilation.owner)
    (unique : NodeOccurrencesUnique view)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations view scope context)
    (readExpression : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerRead : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafLowerer : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (readStatement : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (representationBinder : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked)
    (lowerBinder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals compilation.owner [])
    (sourceCells : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (lowerExpression : policy.lowerExpression = SourceCoreGeneralFunctions.lowerContextualExpression program representation
      signatures locals parents assignments diagnostics compilation (some native) parent skipInitializer)
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {fellThrough escaped : Word}
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (syntaxTree : BuiltinLexicalStatements.Syntax view context true statements expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel view scope statements type reasonAt fellThrough escaped = .ok code) :
    ∃ flow, code = CompatibleStatements.finish type flow fellThrough escaped ∧
      BuiltinLexicalStatements.Tree layouts owner active frame globals onError readFuel values source compilation.solvedRequirements reasonAt
        context scope true statements expected type flow := by
  obtain ⟨flow, same, tree⟩ := BuiltinLexicalStatements.tree_of_contextual_body ordinary unique closed residual
    sourceSignatures declarations readExpression lowerRead leafLowerer readStatement representationBinder lowerBinder sourceCells
    lowerExpression syntaxTree projection accepted
  exact ⟨flow, same, CallableLambdaViewBuiltinBodyTree.original edited avoids tree⟩

private def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α :=
  SourceCompilerFeatureSupport.get label
private def require := SourceCompilerFeatureSupport.require

/-- Existing integer-result admission is used without changing stage rules.
The explicit local function type keeps each real emitted lambda monomorphic. -/
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function mixed(seed: Word, branch: Bool) returns (integer) { let f: function() returns (integer) = lam() -> integer { let missing: Word; let x: Word = wordFromInteger(integerAdd(wordToInteger(seed), 2)); { let nested: Word = wordFromInteger(integerSub(wordToInteger(x), 1)); wordToInteger(nested); } if (branch) { let delta: Word = wordFromInteger(integerSub(wordToInteger(x), wordToInteger(seed))); return wordToInteger(delta); } else { integerEq(wordToInteger(x), wordToInteger(seed)); } return wordToInteger(x); }; return f(); }",
    "function returned(seed: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { wordToInteger(seed); return integerSub(wordToInteger(seed), 1); }; return f(); }",
    "function unit(seed: Word) returns (integer) { let f: function() = lam() { { wordToInteger(seed); } return; }; f(); return wordToInteger(seed); }",
    "function empty() returns (integer) { let f: function() = lam() { }; f(); return 0; }",
    "function failed(seed: Word) returns (integer) { let f: function() returns (integer) = lam() -> integer { let m: mapping(Bool => Word); let warm: Word = m[false]; let missing: Word; { wordToInteger(seed); } return integerAdd(wordToInteger(warm), wordToInteger(missing)); }; return f(); }"]}] }

private def inspect (entry : SourceCompilerFeatureSupport.Entry) : IO Unit := do
  let indexed := entry.cached.indexed
  let base := indexed.base
  let checked := entry.cached.compatible.checked
  let values := SourceCoreCompatibleValues.Context.initial checked
  let mut count := 0
  for template in indexed.ancestry.templates.lambdas do
    let original := template.context.inventory.source
    let .lambda [] _ statements := template.node.form | throw (IO.userError "builtin body view zero-parameter lambda missing")
    let caller ← get "builtin body view owner" (SourceCompilationPlan.exactSpecialization base.plan template.owner)
    let changed := SourceCoreEvidence.withNode original {template.node with type := .unit}
    let compilation : SourceCoreFunctions.Context := {
      plan := base.plan, globals := base.globals, owner := template.owner, administrativePrefix := 1,
      solvedRequirements := caller.function.solvedRequirements, internalReason := Word.zero }
    let scope ← original.inputs.reverse.mapM fun binder => do
      pure (binder.id, ← get "builtin body view scope" (checked.catalog.project binder.scheme.body))
    let expressions := {SourceCoreCompatibleDataExpressions.functionPolicy 200 values with
      callables := SourceCoreGeneralFunctions.callablePolicy (some indexed.ancestry.graph.inputs.callable) template.active}
    let allocate := indexed.layouts.allocatorAt template.owner template.active (fun error => .sourceAllocation (reprStr error))
    let policy : SourceCoreLoops.Policy := {
      lowerExpression := fun fuel source scope id reason => SourceCoreFunctions.lowerExpressionWithPolicy expressions
        (fun _ _ _ _ _ _ _ _ _ => .ok .unit) fuel compilation source scope id reason
      readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
      lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
      sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator indexed.ancestry.layout.frame
        base.globals.length allocate) }
    let before ← get "original builtin lexical body" (SourceCoreLoops.lowerStatementsWithPolicy policy 500 original scope
      statements template.resultType (fun _ => Word.zero) Word.zero Word.zero)
    let after ← get "view builtin lexical body" (SourceCoreLoops.lowerStatementsWithPolicy policy 500 changed scope
      statements template.resultType (fun _ => Word.zero) Word.zero Word.zero)
    require (before == after) "lambda header view changed builtin body/control/marked allocation code"
    require (original != changed) "builtin body view failed to change the actual lambda header"
    require (SourceCoreDataPlaces.declaredBinders original == SourceCoreDataPlaces.declaredBinders changed)
      "builtin body view changed the original binding metadata"
    count := count + 1
  require (count == 1) s!"builtin body view expected one emitted lambda, found {count}"

def run : IO Unit := do
  let program ← get "builtin body view checker" (checkProgram workspace)
  let seed := SourceCompilerFeatureSupport.scalar 7
  let cases : List (String × List SourceCoreExecution.Value × SourceCoreExecution.Value) := [
    ("mixed", [seed, .bool true], .integer 2), ("mixed", [seed, .bool false], .integer 9),
    ("returned", [seed], .integer 6), ("unit", [seed], .integer 7), ("empty", [], .integer 0)]
  for (name, arguments, expected) in cases do
    let entry ← SourceCompilerFeatureSupport.compileNamed program name
    inspect entry
    require ((← entry.run arguments) == expected) s!"builtin body view {name} changed lexical result"
    for fuel in [0, 10, 100] do
      entry.checkResume arguments expected fuel
  let entry ← SourceCompilerFeatureSupport.compileNamed program "failed"
  inspect entry
  let complete ← entry.invoke [seed]
  let (reason, heapSize) ← match complete.outcome with
    | .failed reason session => pure (reason, session.heapSize)
    | _ => throw (IO.userError "builtin body view failure did not remain a language fault")
  let audited ← entry.audit [seed]
  let cells := (SourceCompilerFeatureSupport.sourceState audited).heap
  require (cells.any fun cell => match cell.value with
    | some (.mapping .bool .word []) => true | _ => false)
    "builtin body view lost lazy mapping initialization before failure"
  require (cells.any fun cell => match cell.value with
    | some (.word value) => value == Word.zero | _ => false)
    "builtin body view lost initialized local before failure"
  require ((cells.filter fun cell => cell.type == .word && cell.value.isNone).length == 1)
    "builtin body view changed the uninitialized faulting cell"
  for fuel in [0, 10, 100] do
    let suspended ← entry.invoke [seed] {SourceCompilerFeatureSupport.executionOptions with executionFuel := fuel}
    let checkpoint ← match suspended.outcome with
      | .outOfFuel checkpoint => pure checkpoint
      | _ => throw (IO.userError "builtin body view fault fixture did not suspend")
    match ← checkpoint.resume 300000 1024 with
    | .failed resumed session =>
      require (resumed == reason && session.heapSize == heapSize) "builtin body view resumed fault/effects changed"
    | _ => throw (IO.userError "builtin body view fault checkpoint changed completion")
  IO.println "lambda builtin body views: same marked let/block/if/discard/return/Unit code, scoped results, failure effects and resume GREEN"

end Tests.SourceCoreCallableLambdaViewBuiltinBodyTree
