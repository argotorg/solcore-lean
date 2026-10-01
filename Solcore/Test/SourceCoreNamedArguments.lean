import Solcore.SourceSemantics.CoreLowering.NamedCallArgumentMeaning
import Solcore.Test.SourceCoreUnifiedCorpusSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.TypedLexicalNamedBody.Certificate.mk

/-! Exact packing, independent ordered source arguments and actual cached
named calls. Argument failures skip global/body entry, while completed calls
retain raw mappings, parameter order, lexical fault writes and checkpoints. -/
set_option autoImplicit false
namespace Tests.SourceCoreNamedArguments
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open NamedCalls.Arguments

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"named_arguments", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "named_arguments.solc"⟩, 0, 0⟩
private def id (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def node (index : Nat) (value : Bool) : ExpressionNode := {
  id := id index, span, type := .bool, form := .reference (if value then "true" else "false") (.builtinBoolean value) }
private def source : TypedSource := { owner, inputs := [], roots := [], nodes := [.expression (node 0 true), .expression (node 1 false)] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def sourceProgram : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceContext : SourceSemantics.Context := .ofSignatures signatures
private def codes : List SourceCoreBasic.LoweredExpr :=
  [⟨.bool, LanguageResult.success (.bool true)⟩, ⟨.bool, LanguageResult.success (.bool false)⟩]

/-- Two independently evaluated source arguments and the actual production
packing helper retain the same order, with arbitrary surrounding stores. -/
theorem ordered_arguments (heap : Dynamic.Heap) (environment : Environment) (store : Store) :
    Dynamic.ExpressionsEvaluate sourceProgram sourceContext [] source [] heap [id 0, id 1]
      [.bool true, .bool false] heap ∧
    Evaluates environment store (SourceCoreCalls.packArguments codes).expression
      (.inRight .word (.pair (.bool true) (.bool false))) store := by
  constructor
  · exact .cons (.intro (node := node 0 true) (lookupExpression?_sound (by rfl)) (.builtinBoolean rfl) .nil)
      (.cons (.intro (node := node 1 false) (lookupExpression?_sound (by rfl)) (.builtinBoolean rfl) .nil) .nil)
  · have first : Evaluates environment store (LanguageResult.success (.bool true)) (.inRight .word (.bool true)) store := .inRight .bool
    have second : Evaluates (.bool true :: environment) store
        ((LanguageResult.success (.bool false)).weakenAt 0) (.inRight .word (.bool false)) store := by
      simp only [LanguageResult.success, Expr.weakenAt]; exact .inRight .bool
    exact LocalSequence.pair_success .bool .bool first second

/-- A failed argument completes the actual call without looking up any
global cell, even if no installed function reference exists in the environment. -/
theorem argument_failure_skips_body (signature : SourceCoreCalls.Signature) (index : Nat)
    (reason internal : Word) (environment : Environment) (store : Store) :
    Evaluates environment store
      (SourceCoreCalls.call signature index (LanguageResult.failure signature.parameterType (.word reason)) internal)
      (.inLeft signature.resultType (.word reason)) store ∧
    (∀ value final, Evaluates environment store
      (SourceCoreCalls.call signature index (LanguageResult.failure signature.parameterType (.word reason)) internal) value final →
      value = .inLeft signature.resultType (.word reason) ∧ final = store) := by
  have failed := SourceCoreCalls.call_argument_failure (signature := signature) (index := index) (internalReason := internal)
    (show Evaluates environment store (LanguageResult.failure signature.parameterType (.word reason))
      (.inLeft signature.parameterType (.word reason)) store from .inLeft .word)
  exact ⟨failed, fun _ _ completed => evaluation_deterministic completed failed⟩

/-- Finite whole helper completion exposes the actual retained body after a
non-Unit packed argument, rather than assuming a native child body execution. -/
theorem packed_body_reflection {signature : SourceCoreCalls.Signature} {index : Nat} {location : Location}
    {caller captured : Environment} {store final : Store} {body arguments : Expr} {argument value : Value}
    (evaluated : Evaluates caller store arguments (.inRight .word argument) store)
    (reference : caller[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (completed : Evaluates caller store (SourceCoreCalls.call signature index arguments Word.zero) value final) :
    Evaluates (argument :: captured) store body value final :=
  body_complete evaluated reference read completed

/-- Actual production acceptance retains the canonical source target and the
ordered child compile receipts. The caller must supply static child trees,
never a semantic body or child execution field. -/
theorem actual_compiler_receipt {compilation : SourceCoreFunctions.Context} {callerSource : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {call callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} {signature : SourceCoreCalls.Signature}
    {arguments : List SourceCoreBasic.LoweredExpr} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Emission compilation callerSource scope call callee ids instantiation signature arguments lowered) :
    lowered.expression = SourceCoreCalls.call signature
      (scope.length + compilation.administrativePrefix + receipt.index)
      (SourceCoreCalls.packArguments arguments).expression compilation.internalReason ∧
    signature.parameterType = (SourceCoreCalls.packArguments arguments).type ∧
    SourceCompilationPlan.exactInstantiationKey compilation.plan instantiation = .ok signature.key ∧
    compilation.globals[receipt.index]? = some signature := receipt.equation

private def content : String := String.intercalate "\n" [
  "enum Item { Item(Bool) }",
  "function identity(value: Bool) returns (Bool) { return value; }",
  "function two(first: Bool, second: Bool) returns (Bool) { return first; }",
  "function accept(item: Item, flag: Bool) returns (Bool) { return flag; }",
  "function fail(value: Bool) returns (Bool) { let written = !value; let gap: Bool; return gap; }",
  "function one(flag: Bool) returns (Bool) { return identity(!flag); }",
  "function many(flag: Bool, raw: mapping(Bool => Bool)) returns (Bool) { let m: mapping(Bool => Bool); return two(m[!flag], raw[flag]); }",
  "function skipped(flag: Bool) returns (Bool) { let m: mapping(Bool => Bool); let gap: Bool; return two(m[flag], gap); }",
  "function missing(flag: Bool) returns (Bool) { let m: mapping(Bool => Item); return accept(m[flag], !flag); }",
  "function fault(flag: Bool) returns (Bool) { return fail(!flag); }",
  "function echo(raw: mapping(Bool => Bool)) returns (mapping(Bool => Bool)) { return raw; }",
  "function forwarded(raw: mapping(Bool => Bool)) returns (mapping(Bool => Bool)) { return echo(raw); }",
  "function through(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { return f; }",
  "function callable(f: function(Bool) returns (Bool), flag: Bool) returns (function(Bool) returns (Bool)) { return through(f, !flag); }"
]

private def cells (initial final : SourceTypedRuntime.RuntimeState)
    (expected : List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) (label : String) : IO Unit := do
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr (final.heap.take initial.heap.length) == reprStr initial.heap)
    s!"named argument prefix changed {label}"
  SourceCoreUnifiedCorpusSupport.assertTrue (reprStr ((final.heap.drop initial.heap.length).map (fun cell => (cell.type, cell.value))) == reprStr expected)
    s!"named argument ordered cells changed {label}: {reprStr final.heap}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  let resumed ← SourceCoreUnifiedCorpusSupport.get s!"named arguments resume {name}" (first.resume 300000)
  pure resumed.observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "named general arguments" content ["one", "many", "skipped", "missing", "fault", "forwarded", "callable"]
  let initialState : SourceTypedRuntime.RuntimeState := {heap := [⟨.comptime .word, none⟩, ⟨.word, some (.word (Word.ofNatModulo 819))⟩]}
  let raw : SourceTypedRuntime.Value := .mapping (.comptime .bool) (.comptime .bool) [(.bool true, .bool true), (.bool true, .bool false)]
  let mappingType : TypeSystem.Ty := .mapping .bool .bool
  let materialized : SourceTypedRuntime.Value := .mapping .bool .bool []
  let identityKey ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "identity"
  let functionValue : SourceTypedRuntime.Value := .global identityKey []
  let item ← SourceCoreUnifiedCorpusSupport.get "named argument Item"
    (match compiled.sourceProgram.signatures.dataTypes.head? with | some item => Except.ok item | none => Except.error "missing Item")
  for fuel in [0, 43, 300000] do
    match ← finish compiled "one" [.bool true] fuel initialState with
    | .done (.bool false) final => cells initialState final [(.bool, some (.bool true)), (.bool, some (.bool false))] "one"
    | other => throw (IO.userError s!"named one changed: {reprStr other}")
    match ← finish compiled "many" [.bool true, raw] fuel initialState with
    | .done (.bool false) final =>
      cells initialState final
        [(.bool, some (.bool true)), (mappingType, some raw), (mappingType, some materialized), (.bool, some (.bool false)), (.bool, some (.bool true))] "many"
    | other => throw (IO.userError s!"named many changed: {reprStr other}")
    match ← finish compiled "forwarded" [raw] fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr raw) "named forwarded raw header/order changed"
      cells initialState final [(mappingType, some raw), (mappingType, some raw)] "forwarded"
    | other => throw (IO.userError s!"named forwarded changed: {reprStr other}")
    match ← finish compiled "callable" [functionValue, .bool true] fuel initialState with
    | .done value final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (reprStr value == reprStr functionValue) "named callable identity changed"
      cells initialState final [(.function .bool .bool, some functionValue), (.bool, some (.bool true)), (.function .bool .bool, some functionValue), (.bool, some (.bool false))] "callable"
    | other => throw (IO.userError s!"named callable argument changed: {reprStr other}")
    match ← finish compiled "skipped" [.bool true] fuel initialState with
    | .fault (.uninitializedLocal actual) final =>
      let specialized ← SourceCoreUnifiedCorpusSupport.get "named skipped source" (SourceCompilationPlan.exactSpecialization compiled.validationPlan
        (← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "skipped"))
      let gap ← SourceCoreUnifiedCorpusSupport.get "named skipped gap"
        (match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).find? (·.name == "gap") with
         | some binder => Except.ok binder | none => Except.error "missing gap")
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap.id) "named argument fault lost source binder"
      cells initialState final [(.bool, some (.bool true)), (mappingType, some materialized), (.bool, none)] "skipped"
    | other => throw (IO.userError s!"named argument fault changed: {reprStr other}")
    match ← finish compiled "missing" [.bool true] fuel initialState with
    | .fault (.typeMismatch rawType none) final =>
      SourceCoreUnifiedCorpusSupport.assertTrue (rawType == .nominal item.id []) "named argument missing default metadata changed"
      cells initialState final [(.bool, some (.bool true)), (.mapping .bool rawType, some (.mapping .bool rawType []))] "missing"
    | other => throw (IO.userError s!"named missing argument changed: {reprStr other}")
    match ← finish compiled "fault" [.bool true] fuel initialState with
    | .fault (.uninitializedLocal actual) final =>
      let specialized ← SourceCoreUnifiedCorpusSupport.get "named body fault source" (SourceCompilationPlan.exactSpecialization compiled.validationPlan
        (← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "fail"))
      let gap ← SourceCoreUnifiedCorpusSupport.get "named body fault gap"
        (match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).find? (·.name == "gap") with
         | some binder => Except.ok binder | none => Except.error "missing gap")
      SourceCoreUnifiedCorpusSupport.assertTrue (actual == gap.id) "named body fault lost source binder"
      cells initialState final [(.bool, some (.bool true)), (.bool, some (.bool false)), (.bool, some (.bool true)), (.bool, none)] "fault"
    | other => throw (IO.userError s!"named body fault changed: {reprStr other}")
  IO.println "named arguments: actual cached calls, ordered packing, argument/body faults, raw mappings/callables and resume GREEN"

end Tests.SourceCoreNamedArguments
