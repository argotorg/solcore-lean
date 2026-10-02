import Solcore.SourceSemantics.CoreLowering.BuiltinImperativeFor
import Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates
import Solcore.Test.SourceCompilerFeatureSupport

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Reachable assignment diagnostics pass through the same ordinary statement,
while/for and header/post Trees. Concrete builtin and named consumers close
child meanings. Equal-only fixtures have an empty actual assignment table;
compound and RHS faults retain their effects and exact diagnostics. Match Ready
and function-body/catalog wrappers remain separate consumers. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreImperativeForReachableDiagnostics
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext)
open CallableIndexedHistory (NativeFrame)
open NamedImperativeForStatements
section Static
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : TypedLexicalWhile.ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
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
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem concrete_named_preserves {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedImperativeForStatements.Tree.preserves_reachable functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree errors

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem concrete_named_reflects {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code :=
  NamedImperativeForStatements.Tree.reflects_reachable functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing tree errors


include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Initializers and the nested body inhabit the same recursive grammar. The
head is followed by its concrete tail with no runtime endpoint premise. -/
theorem concrete_for_preserves {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm}
    {condition : ExpressionId} {statements rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (initial : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.initializers items condition post statements) expected type initialCode)
    (initialErrors : GenericImperativeFor.Tree.ReachableErrors registry faults initial)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode rest) expected type body)
    (tailErrors : GenericImperativeFor.Tree.ReachableErrors registry faults tail) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type initialCode body) :=
  concrete_named_preserves functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.forLoop found form initial tail)
    (.forLoop (found := found) (form := form) initialErrors tailErrors)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Completed initializers, finite iterations and post are inverted before the
tail. Break/return skip post and continue/fallthrough run it in source order. -/
theorem concrete_for_reflects {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool}
    {id : StatementId} {node : StatementNode} {items post : List ForItemForm}
    {condition : ExpressionId} {statements rest : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode body : Expr} {administrative : Core.Context}
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop items condition post statements)
    (initial : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.initializers items condition post statements) expected type initialCode)
    (initialErrors : GenericImperativeFor.Tree.ReachableErrors registry faults initial)
    (tail : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode rest) expected type body)
    (tailErrors : GenericImperativeFor.Tree.ReachableErrors registry faults tail) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals) (scope := scope)
      mode (id :: rest) expected type (LocalLoop.sequence type initialCode body) :=
  concrete_named_reflects functions definitions registered extension faithful observations runtimeViews evidence
    unique owners uninitialized missing bodyUninitialized bodyMissing (.forLoop found form initial tail)
    (.forLoop (found := found) (form := form) initialErrors tailErrors)

end Static

section Builtin
open BuiltinImperativeFor
open TypedScopedStatements (Executes)
open TypedLexicalWhile (FlowRep)
open TypedLexicalControl (LexicalResult)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : TypedLexicalWhile.ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem concrete_builtin_preserves {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : BuiltinImperativeFor.Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply BuiltinImperativeFor.Tree.preserves_reachable (functions := functions) (tree := tree)
  all_goals assumption

include definitions registered extension uninitialized missing faithful observations functionTypes in
theorem concrete_builtin_reflects {context : SourceSemantics.Context} {scope : TypedLexicalWhile.Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : BuiltinImperativeFor.Tree layouts owner active frame globals onError readFuel values source solved reasonAt ambient.definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  apply BuiltinImperativeFor.Tree.reflects_reachable (functions := functions) (tree := tree)
  all_goals assumption

end Builtin

section Receipt
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : TypedLexicalWhile.ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context} {scope : TypedLexicalWhile.Scope} {type : Ty}
  {assignment : AssignmentResolution} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head values source context (certificates context) scope administrative definitions assignment .equal rhs)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (missing : ∀ {root resolved reason token count},
    CompatibleMixedRoute.FaultToken values.checked registry root head.prepared.steps resolved reason token count → faults reason token)
  (uninitialized : ∀ location, faults (.uninitializedLocation location) head.prepared.invalidProjection)

include missing uninitialized in
/-- Equal introduces no operand-token law at a statement position. -/
theorem equal_statement_receipt {id : StatementId} {node : StatementNode} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment .equal rhs)
    (tail : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tail) :
    GenericImperativeFor.Tree.ReachableErrors registry faults (.assign found form head tail) :=
  .assign (found := found) (form := form) errors
    (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

include missing uninitialized in
/-- The initializer position uses exactly the same policy and static Tree. -/
theorem equal_initializer_receipt {items post : List ForItemForm} {condition : ExpressionId}
    {statements : List StatementId} {expected : TypeSystem.Ty} {code : Expr}
    (tail : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative
      context scope (.initializers items condition post statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tail) :
    GenericImperativeFor.Tree.ReachableErrors registry faults (.initializerAssign head tail) :=
  .initializerAssign errors (GenericAssignmentStatements.Head.ReachableErrors.equal missing uninitialized)

/-- The reachable receipt cannot be strengthened to the old operand law for
an empty diagnostic interpretation. -/
theorem equal_strict_impossible (noOperand : ∀ token, ¬ faults (.invalidAssignmentOperands .equal) token) :
    ¬ head.Errors registry faults := by
  intro errors
  exact noOperand _ errors.operands

end Receipt

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function copied(value: Word) returns (Word) { let local = value; return local; }",
    "function bad(value: Word) returns (Word) { let local = value; let gap: Word; return gap; }",
    "function equalLoops(seed: Word) returns (Word) { let result = 0; for (let outer: Word, outer = copied(0); outer < 1; let post: Word, post = copied(outer + 1), outer = post) { let inner = 0; while (inner < 1) { result = copied(seed); inner = inner + 1; if (inner < 1) { continue; } break; } } return result; }",
    "function builtinEqual(seed: Word) returns (integer) { let root = wordFromInteger(wordToInteger(seed)); for (root = wordFromInteger(wordToInteger(seed)); integerEq(wordToInteger(root), wordToInteger(seed)); root = 99) { break; } return wordToInteger(root); }",
    "function returnSkipsPost(seed: Word) returns (Word) { let root = 0; for (let index = 0; true; root = bad(seed)) { while (true) { root = copied(seed); return root; } } return 99; }",
    "function bodyRhsFault(seed: Word) returns (Word) { let root = 1; for (let index = 0; true; root = 99) { while (true) { root = copied(seed); root = bad(seed); } } return 99; }",
    "function bodyCompound(seed: Word) returns (Word) { let root: Word; for (let index = 0; true; index = 99) { while (true) { index = copied(1); root += copied(seed); } } return 99; }",
    "function postRhsFault(seed: Word) returns (Word) { let root = 0; for (let index = 0; true; let post: Word, post = bad(seed), root = 99) { root = copied(seed); continue; } return 99; }"
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
  let program ← get "reachable imperative fixtures" (checkProgram workspace)
  for (name, expectedCells) in [
      ("equalLoops", [some 7, some 7, some 1, some 0, some 0, some 1, some 7, some 7, some 1, some 1, some 1]),
      ("builtinEqual", [some 7, some 7]),
      ("returnSkipsPost", [some 7, some 7, some 0, some 7, some 7])] do
    let entry ← compileNamed program name
    let source ← sourceFor entry name
    let table ← get "equal statement/loop table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
    require (table.sites.isEmpty && table.diagnostic? Word.zero == none)
      "ordinary equal introduced an unreachable operand token"
    let expected : SourceCoreExecution.Value := if name == "builtinEqual" then .integer 7 else scalar 7
    require ((← entry.run [scalar 7]) == expected) "equal loop control or scope changed"
    entry.checkCells [scalar 7] (cells expectedCells)
    let complete ← entry.audit [scalar 7]
    for fuel in [0,7,43] do
      entry.checkResume [scalar 7] expected fuel
      let pending ← entry.audit [scalar 7] fuel
      let resumed ← get "native equal loop resume" (pending.resume 300000)
      require ((← nativeObservation complete) == (← nativeObservation resumed))
        "equal resume changed the complete native store"
  for (name, expectedCells) in [
      ("bodyRhsFault", [some 7, some 7, some 0, some 7, some 7, some 7, some 7, none]),
      ("postRhsFault", [some 7, some 7, some 0, some 7, some 7, none, some 7, some 7, none])] do
    let entry ← compileNamed program name
    let source ← sourceFor entry name
    let table ← get "RHS-failed equal table" (SourceCoreAssignmentFaultSites.prepare source Core.wordModulus)
    require table.sites.isEmpty "RHS failure introduced an equal operand token"
    let badSource ← sourceFor entry "bad"
    let (node, binder) ← match badSource.nodes.findSome? fun
        | .expression node => match node.form with | .reference "gap" (.local binder) => some (node,binder) | _ => none
        | _ => none with
      | some selected => pure selected | none => throw (IO.userError "callee failure occurrence missing")
    failure entry {error := .uninitializedLocal binder, site := .occurrence node.id.occurrence, span := some node.span}
      (cells expectedCells)
  let entry ← compileNamed program "bodyCompound"
  let source ← sourceFor entry "bodyCompound"
  let table ← get "compound body table" (SourceCoreAssignmentFaultSites.prepare source 100)
  let node ← match source.nodes.findSome? fun
      | .statement node => match node.form with | .assignValue _ .add _ => some node | _ => none
      | _ => none with
    | some selected => pure selected | none => throw (IO.userError "compound body occurrence missing")
  require (table.length == 1 && table.sites.all fun site => decide
    (site.site = .occurrence node.id.occurrence ∧ site.span = node.span ∧ site.rhsType = .word ∧ site.kind = .value .add))
    "compound body lost exact raw fault metadata"
  failure entry {
    error := .invalidAssignmentOperands .add none (some .word),
    site := .occurrence node.id.occurrence, span := some node.span}
    (cells [some 7, none, some 1, some 1, some 1, some 7, some 7])
  IO.println "reachable imperative/for diagnostics: same grammar, empty equal table, concrete builtin/named children, exact effects/faults and resume GREEN"

end Tests.SourceCoreImperativeForReachableDiagnostics
