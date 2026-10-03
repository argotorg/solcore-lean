import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
import Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionFallthrough
import Solcore.Test.SourceCoreRecursiveNamedLexicalTreeBounds
import Solcore.SourceSemantics.CoreLowering.ReachableStatementContinuationMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! The existing lexical Tree admits terminal non-Unit block/if annotations.
Its stopped suffix is still the exact issued code, while source and original
native witnesses show that it is not executed. Concrete final consumers close
expression meaning using the existing named/Builtin family. The independent
source Syntax receipt and compiler acceptance remain separate; whole for/match
source-syntax extraction is a later unit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreReachableLexicalStatements
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof CallableAncestryPairedLookup
open CallableIndexedHistory SourceCoreCallableIndexedFrames RecursiveNamedCatalog

section Syntax
variable {source : TypedSource} {context : SourceSemantics.Context} {expressionSyntax : ExpressionId → Prop}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest left right : List StatementId}
  {expected : TypeSystem.Ty} {condition : ExpressionId} {conditionNode : ExpressionNode}

theorem actual_nonunit_block_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .block left) (annotation : node.type = expected)
    (inner : GenericLexicalStatements.Syntax source expressionSyntax context false left expected)
    (stops : GenericLexicalStatements.Stopped source left) :
    GenericLexicalStatements.Syntax source expressionSyntax context mode (id :: rest) expected :=
  .terminalBlock unique found form annotation inner stops

theorem actual_nonunit_if_syntax
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition left (some right)) (annotation : node.type = expected)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (typed : ExpressionHasType source context condition conditionNode.type)
    (conditionSyntax : expressionSyntax condition)
    (thenSyntax : GenericLexicalStatements.Syntax source expressionSyntax context false left expected)
    (elseSyntax : GenericLexicalStatements.Syntax source expressionSyntax context false right expected)
    (thenStops : GenericLexicalStatements.Stopped source left)
    (elseStops : GenericLexicalStatements.Stopped source right) :
    GenericLexicalStatements.Syntax source expressionSyntax context mode (id :: rest) expected :=
  .terminalIf unique found form annotation conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops

/-- Reachable nil remains restricted; terminality cannot authenticate an empty list. -/
theorem reachable_nil_nonunit (nonunit : expected ≠ .unit) :
    ¬ GenericLexicalStatements.Syntax source expressionSyntax context true [] expected := by
  intro tree
  cases tree with
  | nil allowed => rcases allowed with impossible | unit; cases impossible; exact nonunit unit

theorem no_empty_stopped : ¬ GenericLexicalStatements.Stopped source [] := by
  rintro ⟨origin, summary, identity, stops⟩
  exact stops.nonempty rfl

/-- Source transport preserves the actual issuing source and callback equation.
It does not assume an arbitrary source-dependent policy accepts the view. -/
theorem original_suffix_transport {origin : TypedSource} {scope : SourceCoreLocalCell.Scope} {type : Ty} {code : Expr}
    (identity : GenericLexicalStatements.StatementSourceIdentity origin source)
    (issued : GenericLexicalStatements.IssuedSuffix origin scope mode rest type code) :
    GenericLexicalStatements.IssuedSuffix source scope mode rest type code :=
  issued.transport identity
end Syntax


section Extraction
open GenericLexicalStatements (Tree Syntax Stopped)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}

theorem accepted_terminal_block (residualMode : Bool)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode} {statements rest : List StatementId} {expected : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (annotation : node.type = expected)
    (inner : Syntax source expressionSyntax context false statements expected)
    (stops : Stopped source statements)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope (id :: rest) type reasonAt mode selfReason = .ok code) :
    Tree layouts owner active frame globals onError values source certificates
      context scope mode (id :: rest) expected type code := by
  exact GenericLexicalStatements.tree_of_flow_with_residual residualMode readPolicy binderPolicy allocationPolicy
    extractExpressions (.terminalBlock unique found form annotation inner stops) closed residual sourceSignatures declarations projection accepted
end Extraction

section Concrete
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {body : BuiltinNamedCalls.Body prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
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
  (bodyUninitialized : ∀ id location, faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  apply RecursiveNamedLexicalTreeBounds.preserves_at functions definitions registered program evidence
    entry_transport entry_binds budget size bounded ?_ tree valid unique
    environments heaps locals agrees actualTyped reference read unmapped installed trace
  intro child within context valid
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_preserves_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid unique owners uninitialized missing budget child within

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
theorem concrete_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope mode statements expected type code) :
    RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  apply RecursiveNamedLexicalTreeBounds.reflects_at functions definitions registered program evidence
    entry_transport entry_binds budget size bounded ?_ tree valid
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  intro child within context valid
  exact SourceCoreRecursiveNamedExpressionTreeBounds.concrete_reflects_at
    functions extension body bodyUninitialized bodyMissing faithful observations runtimeViews
    valid uninitialized missing budget child within
include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_block_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {innerCode suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false statements expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix) := by
  exact concrete_preserves_at functions definitions registered extension faithful observations runtimeViews
    evidence unique owners uninitialized missing bodyUninitialized bodyMissing budget size bounded
    (.terminalBlock exactUnique found form inner stops issued)

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_block_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {statements rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {innerCode suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (inner : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false statements expected type innerCode)
    (stops : GenericLexicalStatements.Stopped source statements)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type innerCode suffix) := by
  exact concrete_reflects_at functions definitions registered extension faithful observations runtimeViews
    evidence uninitialized missing bodyUninitialized bodyMissing budget size bounded
    (.terminalBlock exactUnique found form inner stops issued)

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_if_preserves_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody elseBody rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
      fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenTree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false thenBody expected type thenCode)
    (elseTree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false elseBody expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    RecursiveNamedLexicalContracts.PreservesAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  exact concrete_preserves_at functions definitions registered extension faithful observations runtimeViews
    evidence unique owners uninitialized missing bodyUninitialized bodyMissing budget size bounded
    (.terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued)

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
theorem terminal_if_reflects_at (budget size : Nat) (bounded : size ≤ budget)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {conditionNode : ExpressionNode} {thenBody elseBody rest : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {conditionCode thenCode elseCode suffix : Expr}
    (exactUnique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition thenBody (some elseBody))
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionType : conditionNode.type = .bool)
    (conditionTree : CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
      fuel values source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (thenTree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false thenBody expected type thenCode)
    (elseTree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source
      (fun context => CompatibleExpressionCalls.Tree (RecursiveNamedCatalog.Head [Header.of_body body] compilation source context)
        fuel values source context solved reasonAt) context scope false elseBody expected type elseCode)
    (thenStops : GenericLexicalStatements.Stopped source thenBody)
    (elseStops : GenericLexicalStatements.Stopped source elseBody)
    (issued : GenericLexicalStatements.IssuedSuffix source scope mode rest type suffix) :
    RecursiveNamedLexicalContracts.ReflectsAt functions program evidence
      (entry := protectedEntry [Header.of_body body] locations capturePrefix compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      size (scope := scope) mode (id :: rest) expected type (LocalLoop.sequence type (LocalLoop.conditional type conditionCode thenCode elseCode) suffix) := by
  exact concrete_reflects_at functions definitions registered extension faithful observations runtimeViews
    evidence uninitialized missing bodyUninitialized bodyMissing budget size bounded
    (.terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued)

end Concrete

private def content : String := String.intercalate "\n" [
  "function both(flag: Bool) returns (Word) { if (flag) { return 7; } else { return 9; } }",
  "function block() returns (Word) { { return 11; } }",
  "function nested(flag: Bool) returns (Word) { let saved = 13; { if (flag) { return saved; } else { return 17; } } }",
  "function reachable(flag: Bool) returns (Word) { if (flag) { return 19; } return 23; }",
  "function dead(flag: Bool) returns (Word) { if (flag) { return 29; } else { return 31; } let gap: Word; gap; }",
  "function failed(flag: Bool) returns (Word) { let prior = 37; if (flag) { let gap: Word; return gap; } else { return 41; } let skipped = 99; return skipped; }",
  "function unit() returns (Unit) { { return; } let gap: Word; gap; }"
]
private def w (n : Nat) : SourceTypedRuntime.Value := .word (Word.ofNatModulo n)
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def require := SourceCoreUnifiedCorpusSupport.assertTrue

private def inspect (compiled : SourceCoreUnifiedCompilation.Compiled) : IO Unit := do
  let prepared := compiled.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "reachable lexical integration missing diagnostics")
    | some diagnostic => pure diagnostic.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "reachable lexical integration parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  let mut terminalAnnotations := 0
  let mut reachableAnnotations := 0
  let mut deadSuffixes := 0
  for named in prepared.base.functions do
    let actual := (CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key []
    let own ← match diagnostics.base.find? named.signature.key with
      | none => throw (IO.userError "reachable lexical integration missing own diagnostics")
      | some own => pure own
    let source := CallableIndexedNamedGeneration.source named
    let scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
    let reasonAt := diagnostics.reasonAt named.signature.key
    let lower := SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram actual
      prepared.base.sourceProgram.signatures prepared.base.locals parents own.assignments diagnostics
      (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext none none
    let policy : SourceCoreLoops.Policy := {
      actual.loopsWithSourceCells actual.expressions.sourceCells named.specialized.function.solvedRequirements
        own.assignments diagnostics named.signature.key lower with
      sourceCells := actual.expressions.sourceCells
      lowerBinder := SourceCoreGeneralFunctions.contextualBinder actual prepared.base.locals named.signature.key [] }
    let statements ← get "reachable lexical integration actual roots"
      (source.roots.mapM (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "reachable lexical integration actual complete body"
      (SourceCoreLoops.lowerStatementsWithPolicy policy prepared.fuel source scope statements
        named.signature.resultType reasonAt own.fellThroughReason own.table.escapedReason)
    let same ← get "reachable lexical integration actual compiler body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    require (body == same) "reachable lexical integration changed actual compiler body"
    for item in source.nodes do
      match item with
      | .statement node =>
          match node.form with
          | .block _ | .ifThen _ _ (some _) =>
              if node.type == .word then terminalAnnotations := terminalAnnotations + 1
          | .ifThen _ _ none =>
              require (node.type == .unit) "reachable one-branch annotation changed"
              reachableAnnotations := reachableAnnotations + 1
          | _ => pure ()
      | _ => pure ()
    match statements with
    | id :: rest =>
        let node ← match source.lookupStatement? id with
          | none => throw (IO.userError "reachable lexical integration root lookup missing")
          | some node => pure node
        match node.form with
        | .ifThen condition left (some right) =>
            let (_, _) ← get "reachable lexical integration actual statement read" (policy.readStatement source id)
            let condition ← get "reachable lexical integration actual condition" (lower (prepared.fuel - 1) source scope condition reasonAt)
            let leftCode ← get "reachable lexical integration actual left"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope left
                named.signature.resultType reasonAt false own.table.escapedReason)
            let rightCode ← get "reachable lexical integration actual right"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope right
                named.signature.resultType reasonAt false own.table.escapedReason)
            let suffix ← get "reachable lexical integration emitted suffix"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy (prepared.fuel - 1) source scope rest
                named.signature.resultType reasonAt true own.table.escapedReason)
            let whole ← get "reachable lexical integration whole flow"
              (SourceCoreLoops.lowerFlowStatementsWithPolicy policy prepared.fuel source scope statements
                named.signature.resultType reasonAt true own.table.escapedReason)
            require (whole == LocalLoop.sequence named.signature.resultType
              (LocalLoop.conditional named.signature.resultType condition.expression leftCode rightCode) suffix)
              "reachable lexical integration did not retain original emitted suffix"
            if !rest.isEmpty then deadSuffixes := deadSuffixes + 1
        | _ => pure ()
    | [] => pure ()
  require (terminalAnnotations >= 6 && reachableAnnotations == 1 && deadSuffixes == 1)
    s!"reachable continuation fixture coverage changed: {terminalAnnotations}/{reachableAnnotations}/{deadSuffixes}"

private def finish (compiled : SourceCoreUnifiedCompilation.Compiled) (name : String)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) (initial : SourceTypedRuntime.RuntimeState) : IO SourceTypedRuntime.RunResult := do
  let first ← SourceCoreUnifiedCorpusSupport.execute compiled name arguments fuel initial
  pure (← get "reachable lexical integration public resume" (first.resume 300000)).observation

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "reachable lexical integration" content
    ["both", "block", "nested", "reachable", "dead", "failed", "unit"]
  inspect compiled
  let initial : SourceTypedRuntime.RuntimeState := {heap := [⟨.word, some (w 821)⟩]}
  let successes : List (String × List SourceTypedRuntime.Value × SourceTypedRuntime.Value × List (TypeSystem.Ty × Option SourceTypedRuntime.Value)) := [
    ("both", [.bool true], w 7, [(.bool, some (.bool true))]),
    ("both", [.bool false], w 9, [(.bool, some (.bool false))]),
    ("block", [], w 11, []),
    ("nested", [.bool true], w 13, [(.bool, some (.bool true)), (.word, some (w 13))]),
    ("nested", [.bool false], w 17, [(.bool, some (.bool false)), (.word, some (w 13))]),
    ("reachable", [.bool true], w 19, [(.bool, some (.bool true))]),
    ("reachable", [.bool false], w 23, [(.bool, some (.bool false))]),
    ("dead", [.bool true], w 29, [(.bool, some (.bool true))]),
    ("dead", [.bool false], w 31, [(.bool, some (.bool false))]),
    ("failed", [.bool false], w 41, [(.bool, some (.bool false)), (.word, some (w 37))]),
    ("unit", [], .unit, [])]
  let baselines ← successes.mapM (fun test => finish compiled test.1 test.2.1 300000 initial)
  let failure ← finish compiled "failed" [.bool true] 300000 initial
  for fuel in [0, 31, 300000] do
    for ((name, arguments, expected, expectedCells), baseline) in successes.zip baselines do
      let observed ← finish compiled name arguments fuel initial
      require (reprStr observed == reprStr baseline) s!"reachable lexical integration full resume changed {name}"
      match observed with
      | .done result final =>
          require (reprStr result == reprStr expected) s!"reachable lexical integration result changed {name}"
          require (reprStr final.heap == reprStr (initial.heap ++ expectedCells.map (fun (type, value) => ⟨type, value⟩)))
            s!"reachable lexical integration ordered heap/dead suffix changed {name}"
      | other => throw (IO.userError s!"reachable lexical integration expected done {name}: {reprStr other}")
    let observed ← finish compiled "failed" [.bool true] fuel initial
    require (reprStr observed == reprStr failure) "reachable lexical integration full fault resume changed"
    match observed with
    | .fault (.uninitializedLocal _) final =>
        require (reprStr final.heap == reprStr (initial.heap ++ [⟨.bool, some (.bool true)⟩, ⟨.word, some (w 37)⟩, ⟨.word, none⟩]))
          "reachable lexical integration fault executed a dead suffix or changed its prefix"
    | other => throw (IO.userError s!"reachable lexical integration expected head fault: {reprStr other}")
  IO.println "reachable lexical integration: actual non-Unit annotations, source stops, original native child, emitted dead suffix and full source heaps/public resume GREEN"

end Tests.SourceCoreReachableLexicalStatements
