import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeInversion
import Solcore.Test.SourceCompilerFeatureSupport

/-! The actual checked cached root supplies native typing for its original
named body. Packed argument and wrapper slots survive the prefix inversion,
including bodies that produce closures. No source body typing is assumed. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedParameterNativeInversion
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CallableIndexedParameterNativeInversion

theorem actual_cached_named_body (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named)
    (global : cached.indexed.base.globals[index]? = some named.signature) :
    ∃ diagnostics code,
      ∃ compiled : CallableIndexedNamedGeneration.Compilation cached.indexed named diagnostics code,
      cached.indexed.secondPass.closures[index]? = some code ∧
      HasType (named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.parameterCode (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions ∧
      HasType (SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
        named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.body (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions :=
  prepared_named_body cached.indexedPrepared member selected global

/-- A frame wrapper cannot conceal a wrongly typed original body. -/
theorem wrong_body_rejected {definitions : DataEnvironment} {context : Core.Context}
    (reference next : Expr) :
    ¬ HasType context (SourceCoreCallableContextFrames.withFrame reference next (.word Word.zero)) .unit definitions := by
  intro typed
  cases withFrame_body typed

/-- The empty parameter fold retains a used raw argument slot. -/
theorem nil_keeps_raw_argument {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
    (definitions : DataEnvironment) (context : Core.Context) :
    HasType (.word :: context) (.var 0) .word definitions :=
  tree_body (CallableIndexedParameterCertificates.Tree.nil
    (layouts := layouts) (owner := owner) (active := active) (layout := frame) (globals := globals)
    (onError := onError) (source := source) (total := 0) (output := .word) (body := .var 0)
    (scope := []) (index := 0)) (.var rfl)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function zero() returns (Word) { return 9; }",
    "function single(value: Word) returns (Word) { return value + 1; }",
    "function order(first: Word, flag: Bool, last: Word) returns (Word) { if (flag) { return first; } return last; }",
    "function recursive(value: Word) returns (Word) { if (value == 0) { return 1; } return single(recursive(value - 1)); }",
    "function make(seed: Word) returns (function(Word, Bool) returns (Word)) { let extra = single(seed); return lam(item: Word, choose: Bool) -> Word { return choose ? extra + item : item; }; }"
  ]}] }

open Tests.SourceCompilerFeatureSupport in
private def checkBodies (entry : Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "actual named diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "actual named parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  require (!prepared.entries.isEmpty) "actual native root missing"
  for (named, index) in prepared.base.functions.zipIdx do
    let own ← match diagnostics.base.find? named.signature.key with
      | some own => pure own | none => throw (IO.userError "actual named diagnostic function missing")
    let statements ← get "actual named roots" ((CallableIndexedNamedGeneration.source named).roots.mapM
      (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "actual named source body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    let parameters ← get "actual named parameter fold"
      (SourceCoreSourceCells.bindParameters (CallableIndexedNamedGeneration.allocator prepared named)
        (CallableIndexedNamedGeneration.source named) [] named.inputs named.signature.resultType
        SourceCoreFunctions.argumentProjection body)
    let output ← get "actual named frame hook"
      (SourceCoreCallableIndexedAncestry.namedBody prepared.ancestry named parameters)
    let cached ← match prepared.secondPass.closures[index]? with
      | some cached => pure cached | none => throw (IO.userError "actual cached closure missing")
    require (cached == .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output)
      "actual body actions did not reproduce the cached closure"
    for root in prepared.entries do
      let context := named.signature.parameterType :: prepared.base.globals.map (·.referenceType) ++
        .cell prepared.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext root.native.inputTypes
      let result := LanguageResult.resultType named.signature.resultType
      require (Core.infer? context parameters prepared.layouts.definitions == some result)
        "actual parameter fold lost native typing"
      require (Core.infer? (CallableIndexedParameterNativeTyping.finalContext named.inputs context)
        body prepared.layouts.definitions == some result) "original named body lost native typing or a wrapper slot"

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "parameter inversion source checker" (checkProgram workspace)
  for (name, arguments, expected) in [
      ("zero", [], scalar 9),
      ("single", [scalar 7], scalar 8),
      ("order", [scalar 11, (.bool false : SourceCoreExecution.Value), scalar 17], scalar 17),
      ("recursive", [scalar 3], scalar 4)] do
    let entry ← compileNamed checked name
    checkBodies entry
    require ((← entry.run arguments) == expected) "actual named body result changed"
    entry.checkResume arguments expected 1
  let entry ← compileNamed checked "make"
  checkBodies entry
  let created ← entry.invoke [scalar 7]
  let done ← match created.outcome with
    | .succeeded done => pure done | _ => throw (IO.userError "actual closure-producing body failed")
  let handle ← match done.value with
    | .function handle => pure handle | _ => throw (IO.userError "actual produced closure missing")
  let packed : SourceCoreExecution.Value := .product (scalar 3) (.bool true)
  let complete ← get "actual produced closure invocation"
    (← done.session.invokePacked handle packed executionOptions)
  let final ← match complete with
    | .succeeded final => pure final | _ => throw (IO.userError "actual produced closure invocation failed")
  require (final.value == scalar 11) "actual captured value or heterogeneous argument order changed"
  let baseline ← get "actual produced closure snapshot" (← final.session.snapshot 2048)
  for fuel in [0, 7, 43] do
    let pending ← get "actual produced closure suspension"
      (← done.session.invokePacked handle packed {executionOptions with executionFuel := fuel})
    let resumed ← match pending with
      | .outOfFuel pending => pending.resume 300000 2048 | complete => pure complete
    match resumed with
    | .succeeded actual =>
      let observed ← get "actual produced closure resumed snapshot" (← actual.session.snapshot 2048)
      require (actual.value == scalar 11 && reprStr observed.cells == reprStr baseline.cells)
        "actual produced closure resume changed parameter allocation or captured state"
    | _ => throw (IO.userError "actual produced closure resume failed")
  IO.println "parameter native inversion: actual cached body actions, zero/single/heterogeneous parameters, recursion, closure capture, hidden slots and resume GREEN"

end Tests.SourceCoreCallableIndexedParameterNativeInversion
