import Solcore.SourceSemantics.CoreLowering.NamedForFunctionBodyMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogProfiles
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.Test.SourceCompilerFeatureSupport

/-! The same named for body and recursive catalog static profile accept reachable
operand diagnostics. Concrete named expression children close the body meaning;
the installed entry and existing callee certificates remain explicit. Actual
equal-only fixtures have no assignment diagnostic entries. Automatic prepared
whole-tree extraction and recursive callee correspondence are separate work. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.NamedForFunctionBody.Certificate.mk
#check_failure Solcore.SourceSemantics.CoreLowering.NamedForFunctionBody.CertificateFor.mk
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.Profile.mk
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.ProfileFor.mk
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.ProfileFor.runtimeMeaning
#check_failure Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog.ProfileFor.bodyMeaning
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreNamedBodyReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAncestryPairedLookup NamedForFunctionBody GeneralHeap ReadOnly CompatiblePayload CoreProof

section CompilerConsumers
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {function : Dynamic.Closure} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem reachable_body_preserves
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  let certificate := of_extracted_for accepted projection generated tree errors
  exact certificate.preserves functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem reachable_body_reflects
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  let certificate := of_extracted_for accepted projection generated tree errors
  exact certificate.reflects functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem reachable_body_finite_iff
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project function.resultType = .ok type)
    {flow : Expr}
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel function.source scope
      function.body type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frameLayout globals onError compilation expressionFuel
      function.source expressionSyntax solved reasonAt administrative
      context scope (.statements true function.body) function.resultType type flow)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  let certificate := of_extracted_for accepted projection generated tree errors
  exact certificate.finite_iff functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed
end CompilerConsumers

section Catalog
open RecursiveNamedCatalog
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
def reachable_catalog_profile
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep} {flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt header.fellThrough header.escaped = .ok header.body)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) header.function.body
      header.output header.reasonAt true header.escaped = .ok flow)
    (tree : GenericImperativeFor.Tree header.layouts header.owner header.active prepared.layout.frame header.globals
      header.onError values header.function.source expressionSyntax
      (fun context => Expressions headers compilation expressionFuel header.function.source context header.solved header.reasonAt)
      ambient.definitions administrative header.context
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (.statements true header.function.body) header.function.resultType header.output flow)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    ProfileFor .reachable headers header compilation expressionFuel expressionSyntax administrative registry faults :=
  ProfileFor.of_extracted accepted projection generated tree errors

/-- The old family keeps its original record; both directions retain its fields. -/
theorem strict_family_adapter
    (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop)
    (administrative : Header prepared values ambient.definitions program → Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profiles : Profiles headers compilation expressionFuel expressionSyntax administrative registry faults) :
    Profiles headers compilation expressionFuel expressionSyntax administrative registry faults :=
  ProfilesFor.to_strict headers compilation expressionFuel expressionSyntax administrative registry faults
    (Profiles.to_for headers compilation expressionFuel expressionSyntax administrative registry faults profiles)
end Catalog

/-- Empty exact operand decoding satisfies the reachable equal law. -/
theorem empty_table_equal (token : Word) :
    AssignmentOperandDiagnostics.OperandsLaw
      (GenericAssignmentDiagnostics.OperandRep ⟨[]⟩) .equal token :=
  AssignmentOperandDiagnostics.equal _ token

theorem no_equal_operand_entry (token : Word) :
    ¬ GenericAssignmentDiagnostics.OperandRep ⟨[]⟩ (.invalidAssignmentOperands .equal) token := by
  rintro ⟨diagnostic, raw, found, _⟩
  cases found


open NamedForFunctionBody in
theorem certificate_record_roundtrip
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
    (certificate : Certificate bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code) : certificate.to_for.to_strict = certificate := by
  cases certificate
  rfl

open RecursiveNamedCatalog in
theorem profile_record_roundtrip
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
    {headers : Inventory prepared values ambient.definitions program}
    {header : Header prepared values ambient.definitions program}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (certificate : Profile headers header compilation expressionFuel expressionSyntax administrative registry faults) : certificate.to_for.to_strict = certificate := by
  cases certificate
  rfl
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function next(value: Word) returns (Word) { return value + 1; }",
    "function less(value: Word, bound: Word) returns (Bool) { return value < bound; }",
    "function bad() returns (Word) { let absent: Word; return absent; }",
    "function equalBody(seed: Word) returns (Word) { let result = seed; for (result = next(seed); less(result, 5); result = next(result)) { let inner = 0; while (less(inner, 2)) { inner = next(inner); } if (result == 3) { continue; } if (result == 4) { break; } } return result; }",
    "function unitBody(seed: Word) { let result = seed; for (result = next(seed); less(result, 3); result = next(result)) { } }",
    "function initialFault(seed: Word) returns (Word) { let result = seed; for (result = bad(); false; result = next(result)) { result = next(result); } return result; }",
    "function postFault(seed: Word) returns (Word) { let result = seed; for (result = next(seed); true; result = bad()) { result = next(result); } return result; }",
    "function bodyFault(seed: Word) returns (Word) { let result = seed; let seen: mapping(Bool => Word); for (result = next(seed); true; result = next(result)) { seen[false] = next(result); result = bad(); } return result; }",
    "function self(n: Word) returns (Word) { let result = 1; for (let i = 0; i < n; i = next(i)) { result = result + self(n - 1); } return result; }"
  ]}]
}
open Tests.SourceCompilerFeatureSupport in
private def verify_resume (entry : Entry) : IO Unit := do
  let baseline ← entry.audit [scalar 1]
  let invocation ← entry.invoke [scalar 1]
  for fuel in [0, 7, 43, 199] do
    let suspended ← entry.audit [scalar 1] fuel
    let resumed ← get "reachable body native resume" (suspended.resume 300000)
    require ((← nativeObservation resumed) == (← nativeObservation baseline))
      "reachable body resume changed native result/store"
    let pending ← entry.invoke [scalar 1] {executionOptions with executionFuel := fuel}
    let terminal ← match pending.outcome with
      | .outOfFuel checkpoint => checkpoint.resume 300000 2048
      | done => pure done
    match invocation.outcome, terminal with
    | .succeeded expected, .succeeded actual =>
      require (actual.value == expected.value) "reachable body resume changed result"
    | .failed expected _, .failed actual session =>
      require (actual == expected) "reachable body resume changed fault token"
      require (decide ((← get "resumed diagnostic" (session.diagnostic entry.key actual)) = (← invocation.diagnostic expected)))
        "reachable body resume changed exact diagnostic"
    | _, _ => throw (IO.userError "reachable body resume changed completion")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "reachable named body checker" (checkProgram workspace)
  for name in ["equalBody", "unitBody", "initialFault", "postFault", "bodyFault", "self"] do
    let entry ← compileNamed checked name
    let item ← get "reachable named source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan entry.key)
    let table ← get "equal-only body table" (SourceCoreAssignmentFaultSites.prepare item.function.typedBody Core.wordModulus)
    require table.sites.isEmpty "equal-only named body requested an unreachable operand token"
    require (table.diagnostic? Word.zero == none) "empty named body table decoded a token"
    verify_resume entry
    let result ← entry.invoke [scalar 1]
    match name, result.outcome with
    | "equalBody", .succeeded completed => require (completed.value == scalar 4) "nested named loop result changed"
    | "unitBody", .succeeded completed => require (completed.value == .unit) "named Unit finish changed"
    | "self", .succeeded completed => require (completed.value == scalar 2) "recursive runtime smoke result changed"
    | _, .failed token _ =>
      require (← result.diagnostic token).isSome "named RHS fault lost its diagnostic"
      let audited ← entry.audit [scalar 1]
      let heap := (sourceState audited).heap
      let expected := if name == "initialFault" then 1 else if name == "postFault" then 3 else 2
      let raw ← get "reachable body expected write" (rawData 128 (scalar expected))
      require (reprStr heap[1]? == reprStr (some (SourceTypedRuntime.Cell.mk .word (some raw))))
        "initializer/body/post fault changed prior writes"
      if name == "bodyFault" then
        let rawMapping ← get "reachable body expected mapping write" (rawData 128
          (.mapping .bool .word [(.bool false, scalar 3)]))
        require (reprStr heap[2]? == reprStr (some (SourceTypedRuntime.Cell.mk (.mapping .bool .word) (some rawMapping))))
          "named RHS fault discarded a completed mapping write"
    | _, _ => throw (IO.userError "unexpected reachable named body completion")
  IO.println "named body reachable diagnostics: same concrete for tree/finish, static recursive profiles, empty equal table, named initializer/body/post faults, prior writes and resume GREEN"
end Tests.SourceCoreNamedBodyReachableDiagnostics
