import Solcore.SourceSemantics.CoreLowering.BuiltinForHeader
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPost
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! One header Tree supports unconditional and reachable diagnostics. Concrete
named children close prefix and post reflection while preserving the installed
entry, actual hidden slots and outer scope. Ordinary equal assignments use no
operand table entry; compound and RHS faults retain their ordered effects.
Whole statement/loop Errors and the match Ready factory remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreForHeaderReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open CallableAncestryPairedLookup (Checked Base)
open CallableIndexedHistory (NativeFrame)

section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_prefix_reflects {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ProtectedForHeader.Result (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  exact ProtectedForHeader.Tree.reflects_reachable functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun current currentValid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_post_reflects
    {administrative : Core.Context} {type : Ty}
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) ambient.definitions administrative type (TypedForHeader.Fallthrough type)
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    (∃ finalContext finalEnvironment after,
      ∃ tail : ProtectedForHeader.Tail (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix) registry functions source solved evidence administrative frame globals contextLocation native
        (TypedForHeader.Fallthrough type) finalContext finalEnvironment after,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧ finalStore = tail.store ∧
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
        tail.mapping tail.world administrative scope environment canonical ambient.definitions ∧
      Dynamic.EnvironmentAgrees after context.locals environment ∧
      RuntimeEnvironmentHasTypes tail.world actual actualContext ambient.definitions ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope tail.mapping tail.world after tail.store canonical) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope finalMap finalWorld after finalStore canonical) := by
  exact ProtectedForHeader.Tree.reflects_post_reachable functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun current currentValid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_named_prefix_fault {administrative : Core.Context} {type : Ty}
    {continuation : SourceSemantics.Context → Scope → Expr → Prop}
    {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : ProtectedForHeader.Tree layouts owner active frame globals onError values source (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact ProtectedForHeader.Tree.preserves_fault_reachable functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun current currentValid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence currentValid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    faithful observations tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed trace

end Concrete

section Receipt
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {scope : Scope} {type : Ty}
  {assignment : AssignmentResolution} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment .equal rhs)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
  (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)

include missing uninitialized in
/-- Equal is valid in the very same static header even when its nonexistent
operand failure has no diagnostic interpretation. -/
theorem equal_header_receipt :
    GenericForHeader.Tree.ReachableErrors registry faults
      (GenericForHeader.Tree.assign (layouts := layouts) (owner := owner) (active := active) (frame := frame)
        (globals := globals) (onError := onError) (type := type) (continuation := TypedForHeader.Fallthrough type)
        head (.nil rfl)) := by
  exact .assign (head := head) (remaining := .nil rfl) (.nil (next := rfl))
    (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

/-- The old stronger premise would require precisely that unreachable token. -/
theorem equal_header_strict_impossible
    (noOperand : ∀ token, ¬ faults (.invalidAssignmentOperands .equal) token) :
    ¬ head.Errors registry faults := by
  intro errors
  exact noOperand _ errors.operands

end Receipt

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function copied(value: Word) returns (Word) { let local = value; return local; }",
    "function bad(value: Word) returns (Word) { let local = value; let gap: Word; return gap; }",
    "function initialEqual(seed: Word) returns (Word) { for (let root: Word, root = copied(seed); false; ) { return 99; } return seed; }",
    "function postEqual(seed: Word) returns (Word) { let outer = 17; let index = 0; for (; index < 1; let outer: Word, outer = copied(seed), index = index + 1) { continue; } return outer; }",
    "function initialCompound(seed: Word) returns (Word) { for (let root: Word, root += copied(seed), let never = 99; true; ) { return 99; } return 99; }",
    "function postCompound(seed: Word) returns (Word) { let index = 0; for (; true; let root: Word, root += copied(seed), let never = 99) { index = index + 1; continue; } return 99; }",
    "function initialRhsFault(seed: Word) returns (Word) { for (let root: Word, root = bad(seed), let never = 99; true; ) { return 99; } return 99; }",
    "function postRhsFault(seed: Word) returns (Word) { let index = 0; for (; true; let root: Word, root = bad(seed), let never = 99) { index = index + 1; continue; } return 99; }"
  ]}]
}

open Tests.SourceCompilerFeatureSupport in
private def sourceFor (entry : Entry) (name : String) : IO TypedSource := do
  let key ← match entry.cached.sourceProgram.signatures.functions.filter (·.name == name) with
    | [signature] => pure (SourceSpecialization.SpecializationKey.mk signature.id [])
    | _ => throw (IO.userError s!"missing checked function {name}")
  let exact ← get "actual specialized source" (SourceCompilationPlan.exactSpecialization entry.cached.validationPlan key)
  pure exact.function.typedBody

open Tests.SourceCompilerFeatureSupport in
private def failure (entry : Entry) (expected : SourceCoreFaultSites.Diagnostic)
    (expectedCells : List (TypeSystem.Ty × Option SourceCoreExecution.Value)) : IO Unit := do
  let invocation ← entry.invoke [scalar 7]
  let token ← match invocation.outcome with
    | .failed token _ => pure token
    | _ => throw (IO.userError "expected a guarded language failure")
  require (token != Word.zero && decide ((← invocation.diagnostic token) = some expected))
    "guarded failure lost the exact decoded diagnostic"
  entry.checkCells [scalar 7] expectedCells
  let complete ← entry.audit [scalar 7]
  match complete.observation with
  | .fault error _ => require (decide (error = expected.error)) "guarded failure priority changed"
  | _ => throw (IO.userError "native source observation lost the failure")
  for fuel in [0, 7, 43] do
    let pending ← entry.audit [scalar 7] fuel
    let resumed ← get "native guarded resume" (pending.resume 300000)
    require ((← nativeObservation resumed) == (← nativeObservation complete))
      "guarded resume changed the failure or actual store prefix"
    let pending ← entry.invoke [scalar 7] {executionOptions with executionFuel := fuel}
    match pending.outcome with
    | .outOfFuel checkpoint =>
      match ← checkpoint.resume 300000 1024 with
      | .failed resumedToken session =>
        let diagnostic ← get "resumed guarded diagnostic" (session.diagnostic entry.key resumedToken)
        require (resumedToken == token && decide (diagnostic = some expected))
          "public guarded resume changed the diagnostic"
      | _ => throw (IO.userError "public guarded resume lost the failure")
    | _ => throw (IO.userError "small guarded budget did not suspend")

open Tests.SourceCompilerFeatureSupport in
private def cells (values : List (Option Nat)) : List (TypeSystem.Ty × Option SourceCoreExecution.Value) :=
  values.map fun value => (.word, value.map scalar)

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let program ← get "reachable for header fixtures" (checkProgram workspace)
  for (name, result, expectedCells) in [
      ("initialEqual", 7, [some 7, some 7, some 7, some 7]),
      ("postEqual", 17, [some 7, some 17, some 1, some 7, some 7, some 7])] do
    let entry ← compileNamed program name
    let source ← sourceFor entry name
    let table ← get "equal header table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
    require (table.sites.isEmpty && table.diagnostic? Word.zero == none)
      "equal header/post requested a nonexistent operand diagnostic"
    require ((← entry.run [scalar 7]) == scalar result) "equal header/post or outer scope changed"
    entry.checkCells [scalar 7] (cells expectedCells)
    for fuel in [0,7,43] do entry.checkResume [scalar 7] (scalar result) fuel
  for (name, priorCells) in [("initialCompound", [some 7]), ("postCompound", [some 7, some 1])] do
    let entry ← compileNamed program name
    let source ← sourceFor entry name
    let table ← get "compound header table" (SourceCoreAssignmentFaultSites.prepare source 100)
    let node ← match source.nodes.findSome? fun
        | .statement node => match node.form with | .forLoop .. => some node | _ => none
        | _ => none with
      | some node => pure node | none => throw (IO.userError "for fault occurrence missing")
    require (table.length == 1 && table.sites.all fun site => decide
      (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.rhsType = .word ∧ site.kind = .value .add))
      "header/post fault table lost owning for occurrence or raw target type"
    failure entry {
      error := .invalidAssignmentOperands .add none (some .word),
      site := .occurrence node.id.occurrence, span := some node.span}
      (cells (priorCells ++ [none, some 7, some 7]))
  for (name, priorCells) in [("initialRhsFault", [some 7]), ("postRhsFault", [some 7, some 1])] do
    let entry ← compileNamed program name
    let ownerSource ← sourceFor entry name
    let table ← get "failed equal header table" (SourceCoreAssignmentFaultSites.prepare ownerSource Core.wordModulus)
    require table.sites.isEmpty "RHS failure caused an equal operand table entry"
    let source ← sourceFor entry "bad"
    let (node, binder) ← match source.nodes.findSome? fun
        | .expression node => match node.form with | .reference "gap" (.local binder) => some (node,binder) | _ => none
        | _ => none with
      | some selected => pure selected | none => throw (IO.userError "named header RHS fault occurrence missing")
    failure entry {
      error := .uninitializedLocal binder,
      site := .occurrence node.id.occurrence, span := some node.span}
      (cells (priorCells ++ [none, some 7, some 7, none]))
  IO.println "reachable for header/post diagnostics: empty equal table, concrete named children, ordered effects, restored scope, exact faults and resume GREEN"

end Tests.SourceCoreForHeaderReachableDiagnostics
