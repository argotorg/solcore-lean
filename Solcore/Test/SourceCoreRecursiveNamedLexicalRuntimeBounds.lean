import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeLexicalBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
import Solcore.Test.SourceCoreRecursiveNamedLexicalTreeBounds
import Solcore.Test.SourceCoreRecursiveNamedWhileRuntimeBounds

/-! The same lexical Tree uses the complete runtime context and actual numeric
literal certificates. The expression law is closed by concrete builtin meaning;
no child or body execution law is a test input. Allocation, scoped restoration,
original source and Core sizes and exact Entry are preserved. Header, for and
catalog mutual closure remain separate boundaries. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreRecursiveNamedLexicalRuntimeBounds
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
#check_failure SourceTypedRuntime.run

section Concrete
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {values : ValuesContext}
  {source : TypedSource} {solved : List SolvedRequirement} {fuel : Nat} {reasonAt : ExpressionId → Word}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (program : SourceSemantics.Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- The actual builtin certificate closes all reached expression leaves. -/
theorem runtime_preserves_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.PreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  apply RecursiveNamedLexicalTreeBounds.preserves_at_for functions definitions registered program evidence transport bindings
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget size bounded ?_ tree valid unique
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  intro child _ context valid
  exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
    (ProtectedExpressionMeaning.preserves_of_typed entry
      (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations runtimeViews
        program evidence valid.ledger valid.runtime unique uninitialized missing)) child

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- Native completion reflects to an independently sized source outcome. -/
theorem runtime_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.ReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (entry := entry) (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  apply RecursiveNamedLexicalTreeBounds.reflects_at_for functions definitions registered program evidence transport bindings
    (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
    (fun valid extended => valid.extend extended) budget size bounded ?_ tree valid
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  intro child _ context valid
  exact RecursiveNamedBoundedContracts.reflects_at_of_unbounded
    (ProtectedExpressionMeaning.reflects_of_typed entry
      (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations runtimeViews
        program evidence valid.ledger valid.runtime uninitialized missing)) child

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- The five-way consumer keeps the same trace, grade, frame and heap. -/
theorem imperative_preserves_at (unique : NodeOccurrencesUnique source)
    (budget size : Nat) (bounded : size ≤ budget) {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      context scope mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code :=
  RecursiveNamedImperativeLexicalBounds.preserves_at_for functions program evidence _
    (runtime_preserves_at functions definitions registered extension faithful observations runtimeViews program evidence
      uninitialized missing transport bindings unique budget size bounded tree)

include definitions registered extension faithful observations runtimeViews uninitialized missing transport bindings in
/-- Reflection also only converts the existing three-way FlowRep. -/
theorem imperative_reflects_at (budget size : Nat) (bounded : size ≤ budget) {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate fuel values source context solved reasonAt)
      context scope mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAtFor functions program evidence
      (fun context => CompatibleRuntimeContextValidity.Valid solved context evidence)
      (administrative := administrative) (entry := entry) (source := source) (context := context)
      (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code :=
  RecursiveNamedImperativeLexicalBounds.reflects_at_for functions program evidence _
    (runtime_reflects_at functions definitions registered extension faithful observations runtimeViews program evidence
      uninitialized missing transport bindings budget size bounded tree)
end Concrete

section Transport
/-- Actual lexical extension keeps every solved row and the same dictionary. -/
theorem binder_runtime_valid {solved : List SolvedRequirement} {context nextContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
    (extended : BinderExtends owner context binder nextContext) :
    CompatibleRuntimeContextValidity.Valid solved nextContext evidence := valid.extend extended

/-- An actual frame and independent program typing supply the initial context. -/
theorem frame_runtime_valid {program : SourceSemantics.Program} {instantiation : DeclarationInstantiation}
    {body : Dynamic.BodyInstance} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {solved : List SolvedRequirement}
    (frame : NamedCalls.SourceFrame program instantiation body function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (programTyped : ProgramWellFormed program) (sameLedger : function.context.solvedRequirements = solved) :
    CompatibleRuntimeContextValidity.Valid solved context function.evidence :=
  CompatibleRuntimeContextValidity.of_frame frame extended programTyped sameLedger

private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def goal : ProgramPredicate := ProgramSignatures.builtinIntPredicate .word
private def row : SolvedRequirement := ⟨⟨0⟩, goal, .assumption goal⟩
private def context : SourceSemantics.Context := (Context.ofSignatures signatures).withSolvedRequirements [row]


/-- The same complete runtime ledger still does not imply ordinary validity. -/
theorem runtime_not_ordinary :
    CompatibleRuntimeContextValidity.Valid [row] context [] ∧
      ¬ CompatibleExpressionLiterals.ContextValid [row] context [] :=
  SourceCoreRecursiveNamedWhileRuntimeBounds.runtime_not_ordinary
end Transport

private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

/-- The original checked source retains a qualified local and every ledger
row. Only its reached bare lexical roots are lowered here; the enclosing
qualified body is a separate compiler boundary. Full code equality includes
both actual scoped children and the issued empty continuation. -/
private def template_lexical : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc", externalLibraries := []
    mainSources := [{path := "main.solc", content := String.intercalate "\n" [
      "trait Mark<T> {}", "impl Mark<Word> {}", "impl Mark<Bool> {}",
      "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
      "function qualified(flag: Bool) returns (Word, Bool) {",
      " { let scoped = false; scoped; }",
      " if (false) { let selected = false; } else { let selected = true; }",
      " { let gap: Bool; gap; }",
      " let f = lam(item) { return keep(item); }; return (f(1), f(flag)); }"
    ]}] }
  let program ← get "runtime lexical checked template source" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "qualified") with
    | [signature] => pure signature
    | _ => throw (IO.userError "runtime lexical qualified signature missing")
  let generic ← match program.functions.filter (·.declaration == signature.id) with
    | [generic] => pure generic
    | _ => throw (IO.userError "runtime lexical qualified body missing")
  let specialized ← get "runtime lexical actual template specialization"
    (SourceSpecialization.specializeFunction signature generic [])
  let source := specialized.function.typedBody
  let ids := source.localSchemeTemplateIds
  let rows := specialized.function.solvedRequirements
  require (!ids.isEmpty && signature.scheme.predicates.isEmpty && specialized.assumptions.isEmpty)
    "runtime lexical template ledger boundary disappeared"
  require (rows.map (·.id) == generic.solvedRequirements.map (·.id))
    "runtime lexical specialization removed or reordered ledger rows"
  for id in ids do
    let row ← match rows.filter (·.id == id) with
      | [row] => pure row
      | _ => throw (IO.userError "runtime lexical unique template row missing")
    match row.evidence with
    | .assumption predicate =>
      require (predicate == row.predicate && !(specialized.assumptions.contains predicate))
        "runtime lexical template was promoted to a declaration assumption"
    | _ => throw (IO.userError "runtime lexical template evidence changed")
  let heads := source.roots.filterMap fun
    | .statement id => (source.lookupStatement? id).bind fun node => match node.form with
      | .block _ | .ifThen _ _ _ => some node
      | _ => none
    | _ => none
  require (heads.length == 3) "runtime lexical actual scoped roots changed"
  let reason : Word := Word.ofNatModulo 827
  let lower := SourceCoreControl.lowerExpressionWithReasons
  let captured := Core.Value.closure .word .word (.var 0) [.word (Word.ofNatModulo 829)]
  let initial : Store := [.word (Word.ofNatModulo 831), captured]
  for (node, index) in heads.zipIdx do
    let (headCode, expectedCells, expectedValue) ← match node.form with
      | .block statements =>
        let child ← get "runtime lexical original block child"
          (SourceCoreControl.lowerFlowStatementsWithExpression lower 299 source [] statements .unit (fun _ => reason) false)
        pure (child,
          (if index == 0 then [.inRight .unit (.bool false)] else [.inLeft .bool .unit]),
          (if index == 0 then .inRight .word (.inLeft .unit .unit)
            else .inLeft (LocalControl.controlType .unit) (.word reason)))
      | .ifThen condition thenBody (some elseBody) =>
        let child ← get "runtime lexical original condition" (lower 299 source [] condition (fun _ => reason))
        let thenCode ← get "runtime lexical original then child"
          (SourceCoreControl.lowerFlowStatementsWithExpression lower 299 source [] thenBody .unit (fun _ => reason) false)
        let elseCode ← get "runtime lexical original else child"
          (SourceCoreControl.lowerFlowStatementsWithExpression lower 299 source [] elseBody .unit (fun _ => reason) false)
        pure (LocalControl.conditional .unit child.expression thenCode elseCode,
          [.inRight .unit (.bool true)], .inRight .word (.inLeft .unit .unit))
      | _ => throw (IO.userError "runtime lexical scoped root form changed")
    let code ← get "runtime lexical actual bare compiler"
      (SourceCoreControl.lowerFlowStatementsWithExpression lower 300 source [] [node.id] .unit (fun _ => reason) false)
    let fullCode := LocalControl.sequence .unit headCode (LocalControl.fallthrough .unit)
    require (code == fullCode) "runtime lexical original child/issued continuation code changed"
    require (source.localSchemeTemplateIds == ids && specialized.function.solvedRequirements == rows)
      "runtime lexical compiler filtered the full source ledger"
    let mut baseline : Option (Core.Value × Store) := none
    for fuel in [10000, 0, 1, 19] do
      let first := runStateful fuel (.initial code [] initial)
      let completed := match first with
        | .outOfFuel checkpoint => runStateful 10000 checkpoint
        | result => result
      match completed with
      | .done value store =>
        require (value == expectedValue) "runtime lexical scoped success/fault result changed"
        require (decide (store = initial ++ expectedCells)) "runtime lexical complete scoped/fault store changed"
        match baseline with
        | none => baseline := some (value, store)
        | some pair => require (decide (pair = (value, store))) "runtime lexical complete captured prefix/resume changed"
      | other => throw (IO.userError s!"runtime lexical native completion failed: {reprStr other}")

def run : IO Unit := do
  template_lexical
  SourceCoreRecursiveNamedLexicalTreeBounds.run
  IO.println "runtime lexical bounds: concrete builtin leaves, same full runtime context, exact lexical allocation/restoration/fault order and resume GREEN"

end Tests.SourceCoreRecursiveNamedLexicalRuntimeBounds
