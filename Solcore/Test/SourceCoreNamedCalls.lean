import Solcore.SourceSemantics.CoreLowering.NamedCallMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBody.Certificate.mk
#check_failure Solcore.Frontend.SourceCoreCompatibleMarkedFunctions.Compilation.mk

/-! Actual cached nil-call/reference selection, a closed independent named Unit
body and concrete installed frame restoration. Checked calls exercise distinct
slots, lexical writes/faults, named output and native suspension/resumption. -/
set_option autoImplicit false
namespace Tests.SourceCoreNamedCalls
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open NamedCalls

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"named_calls", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Solcore.Syntax.SourceSpan := ⟨⟨.main, "named_calls.solc"⟩, 0, 0⟩
private def syntaxMetadata : Solcore.Syntax.FunctionDecl := {
  span, value := {
    signature := {
      span
      name := ⟨span, "unit"⟩
      genericParameters := none
      parameters := ⟨span, []⟩
      modifiers := ⟨none, none⟩
      returnsClause := none
      whereClause := none }
    body := ⟨span, []⟩ } }
private def signatureMetadata : ProgramFunctionSignature := {
  id := owner, name := "unit", parameters := [], returnTypes := [], returnComptime := false,
  scheme := {parameters := [], predicates := [], body := .function .unit .unit}, source := syntaxMetadata }
private def signatures : ProgramSignatures := ⟨[signatureMetadata], [], [], [], [], []⟩
private def source : TypedSource := {owner, inputs := [], roots := [], nodes := []}
private def definition : BodyDefinition := {
  owner, type := .function .unit .unit, resultType := .unit, returnComptime := false,
  solvedRequirements := [], source }
private def program : SourceSemantics.Program := ⟨signatures, [⟨definition⟩], []⟩
private def instantiation : DeclarationInstantiation := {
  declaration := owner, parameterSubstitution := [], type := .function .unit .unit,
  predicates := [], parameterComptime := [], returnComptime := false }
private def context := declarationContext signatures owner [] [] []
private def bodyInstance : Dynamic.BodyInstance := ⟨context, source, .unit⟩
private def function : Dynamic.Closure := ⟨[], .unit, [], source, [], context, []⟩

private theorem valid : SourceSemantics.DeclarationInstantiation.Valid (Context.ofSignatures signatures) instantiation := by
  apply SourceSemantics.DeclarationInstantiation.Valid.intro signatureMetadata
  · exact .head _
  · rfl
  · exact SourceSemantics.ParameterSubstitution.exact_empty
  · intro _ _ member; cases member
  · rfl
  · rfl
  · rfl
  · rfl
private theorem frame : NamedCalls.SourceFrame program instantiation bodyInstance function := by
  constructor
  · apply Dynamic.FunctionInstantiates.intro (signature := signatureMetadata) (definition := ⟨definition⟩)
    · exact .head _
    · exact .head _
    · rfl
    · rfl
    · exact valid
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact .nil
  · constructor
    · intro _ _ lookup; cases lookup
    · intro _ member; simp [bodyInstance, context, declarationContext, Context.withSolvedRequirements,
        Context.withAssumptions, Context.withResidualTypeVariables, Context.forDeclaration, Context.ofSignatures] at member

/-- The declaration body is independently instantiated and executed. The named
bridge reconstructs the real global application without a fabricated lambda. -/
theorem empty_source_call (before : Dynamic.Heap) :
    NamedCalls.BodyOutcome program bodyInstance [] before [] (.value .unit) before ∧
    FunctionCallBody.Outcome program (Context.ofSignatures signatures) [] [] before
      (.global ⟨instantiation, []⟩) [] (.value .unit) before := by
  have body : NamedCalls.BodyOutcome program bodyInstance [] before [] (.value .unit) before :=
    frame.body_of_trace (MonoBindersExtend.nil context) (Dynamic.BindersAllocate.nil [] before)
      (FunctionCallBody.Trace.unit rfl (Dynamic.FunctionStatementsExecute.nil))
  exact ⟨body, frame.call body⟩

private def emptyCode (fellThrough escaped : Word) : Expr :=
  CompatibleStatements.finish .unit (LocalLoop.fallthrough .unit) fellThrough escaped

private theorem empty_lowering (policy : SourceCoreLoops.Policy) (fuel : Nat) (bodySource : TypedSource)
    (fellThrough escaped : Word) (reasonAt : ExpressionId → Word) :
    SourceCoreLoops.lowerStatementsWithPolicy policy fuel bodySource [] [] .unit reasonAt fellThrough escaped =
      .ok (emptyCode fellThrough escaped) := by
  simp only [SourceCoreLoops.lowerStatementsWithPolicy, SourceCoreLoops.lowerFlowStatementsWithPolicy]
  rfl

/-- Actual cached success supplies an empty-body syntax receipt. No source or
native body execution is stored in the predicate consumed by the compiler. -/
theorem cached_empty_named
    {checked : SourceCoreCompatibleCatalog.Checked} (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {slot : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : prepared.base.functions[slot]? = some named)
    (roots : named.specialized.function.typedBody.roots = [])
    (inputs : named.inputs = []) (result : named.signature.resultType = .unit)
    {parents : List SourceCoreLocalEvidence.Prepared} {own : SourceCoreProgramFaultSites.Function}
    (parentReceipt : SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)) = .ok parents)
    (diagnosticReceipt : ∀ diagnostic, prepared.base.diagnostics = some diagnostic →
      (match prepared.base.callableContext with
        | none => diagnostic.program
        | some native => {diagnostic.program with rootTable := native.diagnostics.rootTable}).base.find? named.signature.key = some own)
    (allocate : SourceCoreSourceCells.Allocator)
    (allocator : ((SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts).atContext
      named.signature.key []).expressions.sourceCells = some allocate) :
    ∃ diagnostic code,
      prepared.base.diagnostics = some diagnostic ∧ prepared.secondPass.closures[slot]? = some code ∧
      Nonempty (NamedCompilationReceipt.Receipt prepared.base.sourceProgram
        (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
        prepared.base.sourceProgram.signatures prepared.base.plan prepared.base.globals
        (match prepared.base.callableContext with
          | none => diagnostic.program
          | some native => {diagnostic.program with rootTable := native.diagnostics.rootTable})
        prepared.base.locals prepared.base.callableContext parents own named [] prepared.fuel allocate
        (fun body => body = emptyCode own.fellThroughReason own.table.escapedReason) code) := by
  obtain ⟨diagnostic, code, available, cached, compiled⟩ := NamedCalls.compiled_at prepared selected
  refine ⟨diagnostic, code, available, cached, ?_⟩
  apply NamedCompilationReceipt.of_accepted roots parentReceipt (diagnosticReceipt diagnostic available) allocator ?_ compiled
  intro body accepted
  unfold NamedCompilationReceipt.bodyRequest at accepted
  rw [inputs, result] at accepted
  simp only [List.reverse_nil, List.map_nil] at accepted
  rw [empty_lowering] at accepted
  exact (Except.ok.inj accepted).symm

private theorem empty_evaluates (fellThrough escaped : Word) (environment : Environment) (store : Store) :
    Evaluates environment store (emptyCode fellThrough escaped) (.inRight .word .unit) store := by
  apply LocalControl.finish_fallthrough .unit
  · exact LocalLoop.toControl_normal _ escaped (LocalLoop.fallthrough_evaluates _ _ _)
  · simpa [LanguageResult.success, Expr.weakenAt] using
      (show Evaluates (.unit :: .inLeft .unit .unit :: environment) store (.inRight .word .unit) (.inRight .word .unit) store from .inRight .unit)

/-- The actual cached installation preserves argument zero and moves the
named hook's administrative reference by the physical global slot count. -/
theorem installed_hook_slot (count globals : Nat) (parameter result : Ty)
    (layout : SourceCoreCallableIndexedFrames.Layout) (index : Int) (body : Expr) :
    SourceCoreCompatibleOutputs.installedTemplate count
      (.lambda parameter (LanguageResult.resultType result)
        (SourceCoreCallableIndexedFrames.withFrame (.var (globals + 1))
          (SourceCoreCallableIndexedDispatch.literal layout (.state index)) body)) =
    .lambda parameter (LanguageResult.resultType result)
      (SourceCoreCallableIndexedFrames.withFrame (.var (count + globals + 1))
        (SourceCoreCallableIndexedDispatch.literal layout (.state index))
        (body.rename (NamedCalls.installationRenaming count).lift)) := by
  rw [NamedCalls.installed_lambda, NamedCalls.withFrame_rename, Expr.rename,
    NamedCalls.installation_reference, CallableIndexedRenaming.literal]

/-- A real accepted indexed hook for the closed Unit body installs its selected
frame and restores the caller. Installation renames the whole hook, including
the administrative reference, at any authentic global slot. -/
theorem empty_installed_call
    {checked : SourceCoreCallableIndexedAncestry.Checked} {base : SourceCoreCallableIndexedAncestry.Base checked}
    (ancestry : SourceCoreCallableIndexedAncestry.Prepared base)
    {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
    (fellThrough escaped : Word)
    (accepted : SourceCoreCallableIndexedAncestry.namedBody ancestry named (emptyCode fellThrough escaped) = .ok code)
    {signature : SourceCoreCalls.Signature} {caller captured : Environment} {store : Store}
    {globalIndex frameLocation globalLocation : Nat} {saved : Value}
    (reference : (.unit :: captured)[ξ (base.globals.length + 1)]? =
      some (.cellRef ancestry.layout.frame.type frameLocation))
    (savedRead : store.read? frameLocation = some saved)
    (globalReference : caller[globalIndex]? = some (.cellRef (OptionalCell.cellType signature.functionType) globalLocation))
    (globalRead : store.read? globalLocation = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) (code.rename ξ) captured))) :
    ∃ origin index metadata,
      ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      CallableIndexedHistory.Carries ancestry.graph.inputs ancestry.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates caller store (SourceCoreCalls.call signature globalIndex (SourceCoreCalls.packArguments []).expression Word.zero)
        (.inRight .word .unit) store := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history ancestry accepted
  have ground : (emptyCode fellThrough escaped).rename ξ = emptyCode fellThrough escaped := by
    simp [emptyCode, CompatibleStatements.finish, LocalControl.finish, LocalLoop.toControl,
      LocalLoop.fallthrough, LanguageResult.success, LanguageResult.failure, LanguageResult.bind,
      Expr.weakenAt, Expr.rename, Renaming.lift]
  have next := CallableIndexedContextFrames.literal_evaluates ancestry.layout.frame (.state index) (saved :: .unit :: captured) store
  rw [← CallableIndexedRenaming.literal ancestry.layout.frame (.state index) (Renaming.insertion 0), Expr.rename_insertion] at next
  have body := empty_evaluates fellThrough escaped (.unit :: saved :: .unit :: captured)
    (store.set frameLocation (SourceCoreCallableIndexedFrames.encode ancestry.layout.frame (.state index)))
  have shifted : ((emptyCode fellThrough escaped).weakenAt 0).weakenAt 0 = emptyCode fellThrough escaped := by
    simp [emptyCode, CompatibleStatements.finish, LocalControl.finish, LocalLoop.toControl,
      LocalLoop.fallthrough, LanguageResult.success, LanguageResult.failure, LanguageResult.bind, Expr.weakenAt]
  have evaluated := CallableContextFrames.withFrame_evaluates (body := emptyCode fellThrough escaped)
    (.var reference) savedRead next (shifted.symm ▸ body)
  have restored : (store.set frameLocation (SourceCoreCallableIndexedFrames.encode ancestry.layout.frame (.state index))).set frameLocation saved = store := by
    rw [List.set_set]
    obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp savedRead
    rw [← same, List.set_getElem_self bound]
  have bodyEvaluation : Evaluates (.unit :: captured) store (code.rename ξ) (.inRight .word .unit) store := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal, ground]
    simpa only [restored] using evaluated
  exact ⟨origin, index, metadata, owned, history, (NamedCalls.installed_call_agreement globalReference globalRead).wrap bodyEvaluation⟩

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function empty() {}",
  "function first() returns (Bool) { return true; }",
  "function middle() returns (Bool) { return first(); }",
  "function unit() { let outer: Word; { let inner = first(); } }",
  "function missing() returns (Bool) { let m: mapping(Bool => Item); let failed = m[true]; return false; }",
  "function last() returns (Bool) { let before = middle(); if (before) { let nested = first(); return nested; } return false; }",
  "function get() returns (function(Unit) returns (Bool)) { return first; }",
  "function through() returns (Bool) { let f = first; return f(); }",
  "function fault() returns (Bool) { let written = first(); let gap: Bool; let failed = gap; return false; }"
]

private def check (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (expected : SourceTypedRuntime.Value) (cells : List (TypeSystem.Ty × Option SourceTypedRuntime.Value))
    (initial : SourceTypedRuntime.RuntimeState) : IO Unit := do
  for fuel in [0, 41, 300000] do
    let first ← SourceCoreUnifiedCorpusSupport.execute compiled name [] fuel initial
    let completed ← SourceCoreUnifiedCorpusSupport.get "named call resume" (first.resume 300000)
    match completed.observation with
    | .done value state =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr expected) s!"nil named value changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (state.heap.take initial.heap.length) == reprStr initial.heap) s!"named prefix changed {name}"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((state.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr cells)
        s!"named lexical cells changed {name}: {reprStr state.heap}"
    | other => throw (IO.userError s!"named nil call failed {name}: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named nil calls" content ["first", "middle", "unit", "missing", "last", "get", "fault", "through", "empty"]
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (.word (Word.ofNatModulo 731))⟩]}
  check compiled "empty" .unit [] initial
  let emptyKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "empty"
  let emptySpecialized ← SourceCoreUnifiedCorpusSupport.get "named actual empty specialization"
    (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan emptyKey)
  SourceCoreUnifiedCorpusSupport.assertTrue (emptySpecialized.function.typedBody.roots.isEmpty && emptySpecialized.function.typedBody.inputs.isEmpty)
    "actual cached empty-body receipt preconditions changed"
  check compiled "first" (.bool true) [] initial
  check compiled "middle" (.bool true) [] initial
  check compiled "unit" .unit [(.word, none), (.bool, some (.bool true))] initial
  check compiled "last" (.bool true) [(.bool, some (.bool true)), (.bool, some (.bool true))] initial
  let firstKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "first"
  check compiled "get" (.global firstKey []) [] initial
  check compiled "through" (.bool true) [(.function .unit .bool, some (.global firstKey []))] initial
  let item ← SourceCoreUnifiedCorpusSupport.get "named missing Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with | some item => Except.ok item | none => Except.error "no Item")
  for fuel in [0, 41, 300000] do
    let result ← SourceCoreUnifiedCorpusSupport.execute compiled "missing" [] fuel initial
    let resumed ← SourceCoreUnifiedCorpusSupport.get "named missing resume" (result.resume 300000)
    match resumed.observation with
    | .fault (.typeMismatch raw none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (raw == .nominal item.id []) "named missing-default metadata changed"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) ==
        reprStr ([(TypeSystem.Ty.mapping .bool raw, some (SourceTypedRuntime.Value.mapping .bool raw []))] : List (TypeSystem.Ty × Option SourceTypedRuntime.Value))) "named missing-default heap changed"
    | other => throw (IO.userError s!"nil named missing-default fault changed: {reprStr other}")
  for fuel in [0, 41, 300000] do
    let result ← SourceCoreUnifiedCorpusSupport.execute compiled "fault" [] fuel initial
    let resumed ← SourceCoreUnifiedCorpusSupport.get "named fault resume" (result.resume 300000)
    let specialized ← SourceCoreUnifiedCorpusSupport.get "named fault source" (SourceCompilationPlan.exactSpecialization compiled.validationPlan (← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fault"))
    let binders := SourceCoreDataPlaces.declaredBinders specialized.function.typedBody
    match resumed.observation, binders.find? (·.name == "gap") with
    | .fault (.uninitializedLocal actual) final, some gap =>
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap.id) "nil named fault lost source binder"
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) ==
        reprStr ([ (TypeSystem.Ty.bool, some (SourceTypedRuntime.Value.bool true)), (.bool, none)] : List (TypeSystem.Ty × Option SourceTypedRuntime.Value))) "nil named fault lost prior writes"
    | other, _ => throw (IO.userError s!"nil named fault changed: {reprStr other}")
  IO.println "named nil calls: actual selection/cached hook, source Unit bridge, installed slot shifts, lexical writes/fault and resume GREEN"

end Tests.SourceCoreNamedCalls
