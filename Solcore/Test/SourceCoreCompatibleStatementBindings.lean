import Solcore.SourceSemantics.CoreLowering.CompatibleStatementBindingMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual marked compiler receipts supply a two-binding semantic certificate.
Runtime regressions use one cached artifact for public calls and source/native
heap audits, including uninitialized failure and continuation resumption. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreCompatibleStatementBindings
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleStatementBindings CompatiblePayload GeneralHeap ReadOnly CallableIndexedHistory

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_bindings", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "bindings.solc"⟩, 0, 1⟩
private def statement (index : Nat) : StatementId := ⟨⟨owner, index⟩⟩
private def binder (index : Nat) : TypedBinder := ⟨⟨owner, index⟩, "local", .mono .word, [], false, none⟩
private def first : StatementNode := ⟨statement 0, span, .unit, .letDecl (binder 0) none⟩
private def second : StatementNode := ⟨statement 1, span, .unit, .letDecl (binder 1) none⟩
private def returned : StatementNode := ⟨statement 2, span, .unit, .returnStmt none⟩
private def source : TypedSource := {
  owner, inputs := [], roots := [0, 1, 2].map (fun index => .statement (statement index)),
  nodes := [.statement first, .statement second, .statement returned] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def initial : SourceSemantics.Context := .ofSignatures signatures
private def firstContext := initial.withLocal (binder 0).id (binder 0).scheme
private def finalContext := firstContext.withLocal (binder 1).id (binder 1).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private theorem firstExtension : BinderExtends owner initial (binder 0) firstContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, initial, SourceSemantics.Context.ofSignatures, signatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, initial, SourceSemantics.Context.ofSignatures]
private theorem secondExtension : BinderExtends owner firstContext (binder 1) finalContext := by
  apply BinderExtends.intro
  · exact {
      owned := rfl
      scheme := {
        binders := by simp [TypeParameterBindersWellFormed, firstContext, initial, SourceSemantics.Context.ofSignatures,
          SourceSemantics.Context.withLocal, signatures]
        quantified_nodup := by simp [binder, TypeSystem.Scheme.mono]
        body := .builtin .word }
      quantified_fresh := by simp [SchemeQuantifiersFresh, binder, TypeSystem.Scheme.mono]
      monomorphic_requirements_empty := by intro; rfl }
  · simp [LocalFresh, firstContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal, binder]
private theorem unique : NodeOccurrencesUnique source := by cbv; decide
private theorem syntaxTree : Syntax source finalContext initial [statement 0, statement 1, statement 2] .unit :=
  .uninitialized (node := first) (by rfl) rfl (by rfl) rfl firstExtension rfl
    (.uninitialized (node := second) (by rfl) rfl (by rfl) rfl secondExtension rfl
      (.body (.returnUnit (node := returned) [] (by rfl) rfl rfl)))
private theorem valid : CompatibleExpressionLiterals.ContextValid [] finalContext [] := by
  refine ⟨rfl, ⟨?_, ?_⟩, ?_⟩
  · simp [RequirementIdsUnique, finalContext, firstContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal]
  · intro requirement member
    simp [finalContext, firstContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
  · constructor
    · intro goal evidence found; cases found
    · intro predicate member
      simp [finalContext, firstContext, initial, SourceSemantics.Context.ofSignatures, SourceSemantics.Context.withLocal] at member
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .unit]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.word, .unit]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def reason := Word.ofNatModulo 29
private def faults : FunctionCalls.FaultRep := fun _ token => token = reason
private def onError (_ : SourceCoreAllocationLayouts.Error) : SourceCoreBasic.Error := .traversalExhausted (.declaration owner)
private def policy (layouts : SourceCoreAllocationLayouts.Prepared) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat) : SourceCoreLoops.Policy := {
  lowerExpression := fun _ _ _ id _ => .error (.missingExpression id)
  readStatement := SourceCoreCompatibleDataExpressions.readStatement checked
  lowerBinder := SourceCoreCompatibleDataExpressions.lowerBinder checked
  sourceCells := some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals (layouts.allocatorAt ⟨owner, []⟩ [] onError)) }

/-- Any actual successful compiler output for the two marked bindings supplies
its complete static tree, including both genuine allocation ledger receipts. -/
private theorem certified {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source []
      [statement 0, statement 1, statement 2] .unit (fun _ => reason) reason reason = .ok code) :
    ∃ flow, code = CompatibleStatements.finish .unit flow reason reason ∧
      Tree layouts ⟨owner, []⟩ [] frame globals onError 10 values source finalContext [] (fun _ => reason)
        initial [] [statement 0, statement 1, statement 2] .unit .unit flow := by
  apply tree_of_body rfl (fun _ _ _ => rfl) rfl ?_ syntaxTree ?_ rfl accepted
  · intro scope budget id node lowered _ _ _ _ generated
    cases generated
  · intro id declared index type selected _
    cases selected

private theorem sourceTrace : Dynamic.FunctionStatementsExecuteOutcome program initial [] source [] ⟨[]⟩
    [statement 0, statement 1, statement 2] finalContext (.returned .unit)
    ⟨[⟨.word, none, none⟩, ⟨.word, none, none⟩]⟩ :=
  .control (.cons (.letUninitialized (lookupStatement?_sound (by rfl)) rfl rfl firstExtension .append)
    (.cons (.letUninitialized (lookupStatement?_sound (by rfl)) rfl rfl secondExtension .append)
      (.singleton (lookupStatement?_sound (by rfl)) (by intro expression; simp [returned])
        (.returnUnit (lookupStatement?_sound (by rfl)) rfl))))

/-- The concrete source allocation order entails finite evaluation of whatever
code the actual marked compiler emitted, in arbitrary typed ambient storage. -/
theorem compiled_preserves {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source []
      [statement 0, statement 1, statement 2] .unit (fun _ => reason) reason reason = .ok code)
    {world administrative actualContext canonical actual store ξ contextLocation native}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [] world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions [] world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native)) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
        .unit .unit (.returned .unit) value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld
        ⟨[⟨.word, none, none⟩, ⟨.word, none, none⟩]⟩ finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [] store finalMap finalStore ∧
      Dynamic.HeapMetadataExtend ⟨[]⟩ ⟨[⟨.word, none, none⟩, ⟨.word, none, none⟩]⟩ := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact (Tree.body_preserves (values := values) (ambient := ambient) (faults := faults) functions definitions registered (.refl _) program [] valid (fun _ _ => rfl) tree
    reason reason unique environments heaps .nil agrees typed reference read sourceTrace).2

/-- Conversely a completed generated body reconstructs source execution;
no supplied source trace or semantic body hypothesis is involved. -/
theorem compiled_reflects {layouts : SourceCoreAllocationLayouts.Prepared} {frame : SourceCoreCallableIndexedFrames.Layout}
    {globals fuel : Nat} {code : Expr} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy (policy layouts frame globals) fuel source []
      [statement 0, statement 1, statement 2] .unit (fun _ => reason) reason reason = .ok code)
    {world administrative actualContext canonical actual store ξ contextLocation native value finalStore}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog checked.catalog) [] world administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents checked values.registry functions [] world ⟨[]⟩ store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (completed : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.FunctionStatementsExecuteOutcome program initial [] source [] ⟨[]⟩
        [statement 0, statement 1, statement 2] finalContext outcome after ∧
      CompatibleStatements.BodyRep (values := values) (registry := values.registry) functions finalMap finalWorld faults
        .unit .unit outcome value ∧
      CompatibleAmbientHeap.HeapRepresents checked values.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends [] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend ⟨[]⟩ after := by
  obtain ⟨flow, rfl, tree⟩ := certified accepted
  exact Tree.body_reflects (values := values) (ambient := ambient) (faults := faults) functions definitions registered (.refl _) program [] valid (fun _ _ => rfl) tree
    reason reason environments heaps .nil agrees typed reference read completed

private def rawWorkspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function ordered() { let first: Word; let second: Bool; return; }",
    "function fail() returns (Bool) { let first: Word; let second: Bool; return second; }",
    "function lazy() returns (Word) { let first: Bool; let second: mapping(Word => Word); return second[8]; }",
    "function early() returns (Bool) { let first: Word; return true; let never: Bool; }"]}] }

def run : IO Unit := do
  let checked ← SourceCompilerFeatureSupport.get "binding checker" (checkProgram rawWorkspace)
  let ordered ← SourceCompilerFeatureSupport.compileNamed checked "ordered"
  SourceCompilerFeatureSupport.require ((← ordered.run []) == .unit) "uninitialized prefix Unit result changed"
  ordered.checkCells [] [(.word, none), (.bool, none)]
  ordered.checkResume [] .unit
  let fail ← SourceCompilerFeatureSupport.compileNamed checked "fail"
  let invocation ← fail.invoke []
  match invocation.outcome with
  | .failed token _ =>
    SourceCompilerFeatureSupport.require (← invocation.diagnostic token).isSome "new local read failure lost its diagnostic"
  | _ => throw (IO.userError "new uninitialized local did not fail")
  fail.checkCells [] [(.word, none), (.bool, none)]
  let lazyEntry ← SourceCompilerFeatureSupport.compileNamed checked "lazy"
  SourceCompilerFeatureSupport.require ((← lazyEntry.run []) == .word Word.zero) "new mapping default changed"
  lazyEntry.checkCells [] [(.bool, none), (.mapping .word .word, some (.mapping .word .word []))]
  let early ← SourceCompilerFeatureSupport.compileNamed checked "early"
  SourceCompilerFeatureSupport.require ((← early.run []) == .bool true) "early return changed"
  early.checkCells [] [(.word, none)]
  IO.println "compatible marked bindings: actual receipts, source order, ambient heap, preservation/reflection, failure and resume GREEN"
end Tests.SourceCoreCompatibleStatementBindings
