import Solcore.SourceSemantics.CoreLowering.CallableIndexedRetainedNamedValues
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityMeaning
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedRetainedNamedValues
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedRetainedNamedValues CompatiblePayload GeneralHeap

theorem complete_source_equality {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {left right : Dynamic.Value} {a b : Word} (first : Identity prepared left a) (second : Identity prepared right b) :
    a = b ↔ left = right := (identity_faithful prepared).equal first second

theorem dictionary_unchanged (source : Dynamic.GlobalFunction) :
    (CallableNamedReversal.global source).evidence = source.evidence ∧
    (CallableNamedReversal.global source).instantiation.type = source.instantiation.type ∧
    CallableNamedReversal.global (CallableNamedReversal.global source) = source :=
  ⟨rfl, rfl, CallableNamedReversal.global_twice source⟩

/-- The actual inferred record, selector and specialization factory supply an
identity receipt without a canonical header/domain equality premise. -/
theorem selected_identity {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {index : Nat} {signature : SourceCoreCalls.Signature}
    {sourceSignature : ProgramFunctionSignature} {function : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {specialized : Specialized} {retained : Evidence}
    {identity : Word}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (specialization : SourceSpecialization.specializeFunction sourceSignature function supplied = .ok specialized)
    (unique : sourceSignature.scheme.parameters.Nodup)
    (next : Nat) (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node
      (CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller) true = .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok retained)
    (number : Word.ofNat? (index + 1) = some identity) :
    Identity prepared (.global ⟨CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller,
      CallableNamedMetadata.environment retained⟩) identity := by
  obtain ⟨row, same⟩ := row_of_inferred prepared plan globals selected record specialization unique next final caller rfl resolved
  rw [same]
  exact .retained (.named row number)

/-- Real full-definition payloads provide all equality laws for the retained
model. Distinct parameter list orders are not identified as source values. -/
theorem compare_from_receipts {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) (comparator : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {mapping : LocationMap}
    {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value}
    (first : (model prepared profile).Represents registry mapping world leftType left a comparator.type)
    (second : (model prepared profile).Represents registry mapping world rightType right b comparator.type)
    (store : Store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent left right) ∧
      Evaluates [a, b] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool result)
        (CompatibleEquality.preparedStore comparator [a, b] store) :=
  CompatibleEquality.prepared_compare_preserves comparator (identity_faithful prepared)
    (observations prepared profile first) (observations prepared profile second) [a, b] store _ _ (.var rfl) (.var rfl)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function first<A, B>(a: A, b: B) returns (A) { return a; }",
    "function second<A, B>(a: A, b: B) returns (A) { return a; }",
    "function firstRef() returns (function(Word, Bool) returns (Word)) { return first; }",
    "function secondRef() returns (function(Word, Bool) returns (Word)) { return second; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey := do
  let found ← match program.signatures.functions.find? (·.name == name) with
    | some found => pure found
    | none => throw (IO.userError s!"missing retained fixture {name}")
  pure ⟨found.id, []⟩

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "retained named checker" (checkProgram workspace)
  let roots ← ["firstRef", "secondRef"].mapM (key program)
  let requests := roots.map fun root => (⟨root.declaration, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"retained named worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "retained named compatible artifact" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "retained named indexed artifact" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut seen := 0
  let mut payloads : List Value := []
  for root in roots do
    let caller ← SourceCompilerFeatureSupport.get "retained caller" (SourceCompilationPlan.exactSpecialization prepared.base.plan root)
    let source := caller.function.typedBody
    let compilation : SourceCoreFunctions.Context := ⟨prepared.base.plan, root, prepared.base.globals, 0, [], Word.zero⟩
    let representation := SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts
    let policy := {representation.expressions with callables := SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) []}
    for raw in source.nodes do
      match raw with
      | .expression node =>
        match node.form with
        | .reference _ (.declaration actual) =>
          let (index, signature) ← SourceCompilerFeatureSupport.get "actual retained selectedSignature"
            (SourceCoreFunctions.selectedSignature policy compilation source node actual true)
          let specialized ← SourceCompilerFeatureSupport.get "retained callee" (SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key)
          let canonical := CallableNamedMetadata.instantiation specialized
          SourceCompilerFeatureSupport.require (actual.parameterSubstitution.length == 2) "fixture lost two distinct type parameters"
          SourceCompilerFeatureSupport.require (decide (actual = CallableNamedReversal.instantiation canonical))
            "actual checked metadata does not equal the reverse-ledger canonical header"
          SourceCompilerFeatureSupport.require (decide (actual ≠ canonical)) "actual and plan ledger order unexpectedly coincide"
          let actualTarget ← SourceCompilerFeatureSupport.get "actual retained exact target" (SourceCompilationPlan.exactInstantiationKey prepared.base.plan actual)
          let canonicalTarget ← SourceCompilerFeatureSupport.get "canonical exact target" (SourceCompilationPlan.exactInstantiationKey prepared.base.plan canonical)
          SourceCompilerFeatureSupport.require (decide (actualTarget = canonicalTarget)) "reverse matching changed target"
          SourceCompilerFeatureSupport.require (prepared.base.globals[index]? == some signature) "selected slot mismatch"
          seen := seen + 1
        | _ => pure ()
      | _ => pure ()
    let initial ← SourceCompilerFeatureSupport.get "retained named suspended" (prepared.runSource root [] 0)
    let resumed := initial.resume 300000
    let direct ← SourceCompilerFeatureSupport.get "retained named direct" (prepared.runSource root [] 300000)
    match resumed.result.native.observation, direct.result.native.observation with
    | .succeeded value store, .succeeded expected finalStore =>
      SourceCompilerFeatureSupport.require (value == expected && store == finalStore) "retained named resume changed captures or store"
      payloads := payloads ++ [value]
    | first, second => throw (IO.userError s!"retained named execution {reprStr first}, {reprStr second}")
  SourceCompilerFeatureSupport.require (seen == 2) "retained metadata fixture omitted an actual occurrence"
  let comparator ← SourceCompilerFeatureSupport.get "retained named equality" (SourceCoreCompatibleDataEquality.prepare 500 automatic.checked (.function (.product .word .bool) .word))
  for (left, i) in payloads.zipIdx do
    for (right, j) in payloads.zipIdx do
      let comparison := CompatibleEquality.comparison comparator (.var 0) (.var 1)
      let store : Store := [.word (Word.ofNatModulo 57)]
      SourceCompilerFeatureSupport.require (runStateful 100000 (.initial comparison [left, right] store) ==
        .done (.bool (i == j)) (CompatibleEquality.preparedStore comparator [left, right] store))
        "retained named identity equality changed"
  IO.println "retained named values: actual two-parameter reverse metadata, distinct source declarations and resumed captures GREEN"
end Tests.SourceCoreCallableIndexedRetainedNamedValues
