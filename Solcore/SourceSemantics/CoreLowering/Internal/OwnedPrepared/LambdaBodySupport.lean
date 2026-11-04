import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenStoredCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.MixedHeads
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.FormationReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NestedEntries
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CallRejection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.TerminalStatementOrigins

/-!
# Prepared callables: lambda body support

Support of empty, return, branching and imperative lambda bodies, and named lambda formation.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
/-! The actual named terminal callback retains one literal lambda Site, its
original compiler view and complete policy. Bootstrap acceptance removes only
unused native input slots before the genuine child typing inversion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)

private theorem native_child
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) :
    HasType (SourceCoreLocalCell.coreContext
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.receipt.child.expression (LanguageResult.resultType terminal.receipt.child.type)
      compiled.indexed.layouts.definitions := by
  have cached := CallableIndexedOwnedNamedPublicProfileExtraction.cached_typed
    terminal.prepared terminal.aligned member
  have original : HasType ((compiled.indexed.base.globals.map (·.referenceType) ++
      [.cell compiled.indexed.ancestry.layout.frame.type]) ++
        SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
      header.named.signature.functionType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions := by
    simpa only [List.append_assoc, List.singleton_append] using cached
  have minimal := NativeExpressionContextSupport.prefix_typing (targetSuffix := []) original
    (by simpa only [List.length_append, List.length_map, List.length_singleton] using
      CallableIndexedOwnedNamedPublicProfileExtraction.cached_supported prepared terminal.prepared terminal.aligned)
  have body := RecursiveNamedCatalogNativeContexts.body_of_cached (suffix := [])
    (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (header := header) (by simpa only [List.append_nil, List.append_assoc, List.singleton_append,
      CallableIndexedAmbient.ambientDefinitions, SourceCoreCompatibleValues.Context.initial] using minimal)
  have child := terminal.receipt.native_child_exact body
  change HasType _ _ _ compiled.indexed.layouts.definitions at child
  simpa only [RecursiveNamedCatalogNativeContexts.bodyPrefix, RecursiveNamedCatalogNativeContexts.bodyScope,
    RecursiveNamedLambdaFormationHeads.nativePrefix, List.append_nil, List.append_assoc, ← header.parameterType] using child

/-- Original Source and output equalities belong to the same chosen Site.
The complete compiler policy is retained before any later recapture. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported)) :
    ∃ produced : Produced (compiled := compiled) header.named parameters result statements header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt := by
  have accepted := terminal.receipt.generated
  have expressionPolicy : header.policy.lowerExpression =
      (RecursiveNamedPreparedHeaders.Prepared.policy terminal.prepared).lowerExpression :=
    congrArg SourceCoreLoops.Policy.lowerExpression terminal.aligned.policy
  rw [expressionPolicy] at accepted
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext terminal.prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    terminal.prepared.compilation.parents terminal.prepared.compilation.own.assignments terminal.prepared.diagnostics
    (context compiled.indexed terminal.prepared.named) compiled.indexed.base.callableContext none none
    terminal.receipt.childFuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) terminal.expression header.reasonAt =
      .ok terminal.receipt.child at accepted
  have nonzero : terminal.receipt.childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have sourceEq : header.function.source = source terminal.prepared.named :=
    header.agreement.source.trans (congrArg source terminal.aligned.named)
  have record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      terminal.prepared.named.signature.key = .ok terminal.prepared.named.specialized := by
    simpa only [terminal.aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record compiled header
  obtain ⟨site, identifier, emitted, binderPolicy, _bodyRecipe, issuedRecipe, view, reasonAt⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact compiled.indexed
      terminal.prepared.compilation (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared terminal.prepared diagnostic) record header.context header.function.evidence [] profile
      (by rw [← sourceEq]; exact LambdaMetadataViews.MetadataView.refl _)
      (by simpa only [← sourceEq] using found) form found rfl owner requirements coercions ordinary read
      (by simpa only [fuelEq] using accepted) (native_child terminal prepared member)
  let rawProduced : Produced (compiled := compiled) terminal.prepared.named parameters result statements header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := binderPolicy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
  have actual : ∃ produced : Produced (compiled := compiled) terminal.prepared.named parameters result statements header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt :=
    ⟨rawProduced, view, reasonAt⟩
  let Property (named : Named) : Prop :=
    ∃ produced : Produced (compiled := compiled) named parameters result statements header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt
  exact Eq.mp (congrArg Property terminal.aligned.named.symm) actual

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLambdaProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
/-! An empty ordinary lambda body has no child expression obligations. Its
actual retained compiler recipe supplies the loop policy and emitted footer;
its original Source frame and parameter context supply static validity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem empty_tree
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {nativeFrame : SourceCoreCallableIndexedFrames.Layout}
    {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {definitions : DataEnvironment} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {result : TypeSystem.Ty} {type : Ty}
    (empty : statements = []) (unit : result = .unit) :
    ∃ tree : GenericImperativeMatch.Tree layouts owner active nativeFrame globals onError values source
      expressionSyntax certificates definitions administrative context scope (.statements true statements)
      result type (LocalLoop.fallthrough type), tree.CatalogSites .reachable registry faults := by
  subst statements
  exact ⟨.body (.nil (.inr unit)) (.nil (.inr unit)),
    .body (syntaxTree := .nil (.inr unit)) (body := .nil (.inr unit))⟩

/-- The two static trees are constructed for the exact compiler view and
original Source. The accepted Code determines the output and footer. -/
theorem of_empty
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (empty : function.body = []) (unit : function.resultType = .unit) :
    ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics expression)
  have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason =
      .ok (LocalLoop.fallthrough code.receipt.resultCore) := by
    exact (congrArg (fun statements => SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      statements code.receipt.resultCore code.reasonAt true code.compilation.internalReason) empty).trans (by simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy])
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  have emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore
      (LocalLoop.fallthrough code.receipt.resultCore) code.compilation.internalReason
      code.compilation.internalReason := Except.ok.inj accepted.symm
  obtain ⟨actualTree, actualSites⟩ : ∃ tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) code.view (expressionSyntax code.view)
      (certificates 0 code.view) compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore
      (LocalLoop.fallthrough code.receipt.resultCore), tree.CatalogSites .reachable registry faults :=
    empty_tree empty unit
  obtain ⟨tree, sites⟩ : ∃ tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) function.source (expressionSyntax function.source)
      (certificates 0 function.source) compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore
      (LocalLoop.fallthrough code.receipt.resultCore), tree.CatalogSites .reachable registry faults :=
    empty_tree empty unit
  exact ⟨{
    toContext := inputs
    frame := frame
    readFuel := 0
    policy := policy
    callback := callback
    flow := LocalLoop.fallthrough code.receipt.resultCore
    generated := generated
    projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections code profile).2
    emitted := emitted
    actualTree := actualTree
    actualSites := actualSites
    tree := tree
    sites := sites
    valid := CallableIndexedLambdaStaticBodySupport.context_valid
      (values := .initial compiled.compatible.checked) code inputs frame sameLedger
    unique := frame.code.graph.nodeOccurrencesUnique }, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReturnLambdaBodySupport
/-! One original return occurrence retains its exact accepted compiler child.
The static trees carry that child identity and independent Source typing;
application meaning is supplied later by the actual recursive body family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReturnLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal Receipt)

def Syntax (expression : ExpressionId) : TypedSource → ExpressionId → Prop := fun _ id => id = expression

def Child (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) :
    Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ _ _ _ id actual => id = expression ∧ actual = lowered

private theorem finish_injective {type : Ty} {left right : Expr} {fellThrough escaped : Word}
    (same : CompatibleStatements.finish type left fellThrough escaped =
      CompatibleStatements.finish type right fellThrough escaped) : left = right := by
  unfold CompatibleStatements.finish LocalControl.finish LocalLoop.toControl LanguageResult.bind at same
  exact (Expr.caseE.inj (Expr.caseE.inj same).1).1

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

private theorem return_tree
    {source : TypedSource} {context : SourceSemantics.Context} {bodyScope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {statement : StatementId} {node : StatementNode}
    {expression : ExpressionId} {expressionNode : ExpressionNode} {result : TypeSystem.Ty}
    {lowered : SourceCoreBasic.LoweredExpr} {type : Ty}
    (body : statements = [statement])
    (found : source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) (statementType : node.type = result)
    (read : source.lookupExpression? expression = some expressionNode) (raw : expressionNode.type = result)
    (typed : ExpressionHasType source context expression expressionNode.type)
    (native : lowered.type = type) :
    ∃ tree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) source (Syntax expression source)
      (Child expression lowered 0 source) compiled.indexed.layouts.definitions administrative context bodyScope
      (.statements true statements) result type (LocalLoop.returnValue type lowered.expression),
      tree.CatalogSites .reachable registry faults := by
  subst statements
  subst type
  let syntaxTree : GenericLexicalStatements.Syntax source (Syntax expression source) context true [statement] result :=
    .returnValue [] found form statementType read raw typed rfl
  let body : GenericLexicalStatements.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) source (Child expression lowered 0 source)
      context bodyScope true [statement] result lowered.type (LocalLoop.returnValue lowered.type lowered.expression) :=
    .returnValue [] found form read raw ⟨rfl, rfl⟩
  exact ⟨.body syntaxTree body, .body (syntaxTree := syntaxTree) (body := body)⟩

/-- The original callback and one accepted terminal child construct both trees
at the actual Source and parameter context. No child execution law is assumed. -/
theorem of_return_view
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {statement : StatementId} {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
    (body : function.body = [statement])
    (found : function.source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) (statementType : node.type = function.resultType)
    (read : function.source.lookupExpression? expression = some expressionNode)
    (raw : expressionNode.type = function.resultType)
    (typed : ExpressionHasType function.source inputs.context expression expressionNode.type)
    (viewFound : code.view.lookupStatement? statement = some node)
    (viewRead : code.view.lookupExpression? expression = some expressionNode)
    (viewTyped : ExpressionHasType code.view inputs.context expression expressionNode.type) :
    ∃ lowered, ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) (Syntax expression) (Child expression lowered)
      code (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax expression function.source)
        body.context (.statements true function.body) function.resultType := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let children := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics children
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower children) recipe
  have callback : code.lowerBody children = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics children)
  have terminal : Terminal code.view expression function.body := by
    rw [body]
    exact .returning [] viewFound form
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (show policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked from rfl)
    terminal accepted
  have generated := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at generated
  obtain ⟨flow, generated, same⟩ := CompatibleEncoding.bind_ok generated
  have sameFlow : flow = LocalLoop.returnValue code.receipt.resultCore receipt.child.expression :=
    finish_injective ((Except.ok.inj same).trans receipt.emitted)
  subst flow
  obtain ⟨actualTree, actualSites⟩ := return_tree code (registry := registry) (faults := faults)
    (source := code.view) (bodyScope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    body viewFound form statementType viewRead raw viewTyped receipt.sameType
  obtain ⟨tree, sites⟩ := return_tree code (registry := registry) (faults := faults)
    (source := function.source) (bodyScope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    body found form statementType read raw typed receipt.sameType
  let result : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) (Syntax expression) (Child expression receipt.child)
      code (Program.ofChecked compiled.sourceProgram) registry faults := {
    toContext := inputs
    frame := frame
    readFuel := 0
    policy := policy
    callback := callback
    flow := LocalLoop.returnValue code.receipt.resultCore receipt.child.expression
    generated := generated
    projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections code profile).2
    emitted := receipt.emitted
    actualTree := actualTree
    actualSites := actualSites
    tree := tree
    sites := sites
    valid := CallableIndexedLambdaStaticBodySupport.context_valid
      (values := .initial compiled.compatible.checked) code inputs frame sameLedger
    unique := frame.code.graph.nodeOccurrencesUnique }
  refine ⟨receipt.child, result, rfl, ?_⟩
  change GenericImperativeMatch.Syntax function.source (Syntax expression function.source)
    inputs.context (.statements true function.body) function.resultType
  simpa only [body] using (show GenericImperativeMatch.Syntax function.source (Syntax expression function.source)
    inputs.context (.statements true [statement]) function.resultType from
    .body (.returnValue [] found form statementType read raw typed rfl))

/-- Identical Source views retain the original convenience interface. -/
theorem of_return
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (view : code.view = function.source)
    {statement : StatementId} {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
    (body : function.body = [statement])
    (found : function.source.lookupStatement? statement = some node)
    (form : node.form = .returnStmt (some expression)) (statementType : node.type = function.resultType)
    (read : function.source.lookupExpression? expression = some expressionNode)
    (raw : expressionNode.type = function.resultType)
    (typed : ExpressionHasType function.source inputs.context expression expressionNode.type) :
    ∃ lowered, ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) (Syntax expression) (Child expression lowered)
      code (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax expression function.source)
        body.context (.statements true function.body) function.resultType := by
  exact of_return_view code retained inputs frame sameLedger profile body found form statementType read raw typed
    (by simpa only [view] using found) (by simpa only [view] using read) (by simpa only [view] using typed)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReturnLambdaBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
/-! Actual named compilation retains the same lambda and its single
return child. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal_parameters
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result [statement] header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have invocationSource : child.source = function.source :=
    (stages.source selected).trans original.symm
  have returnFound : function.source.lookupStatement? statement = some returnNode := by
    simpa only [original] using returnFound
  have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression function.body := by
    change CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression [statement]
    exact .returning [] (by rw [invocationSource]; exact lookupStatement?_sound returnFound) returnForm
  obtain ⟨readNode, childFound, childType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters frame inputs.extended invocationSource head
  rw [invocationSource] at childFound childTyped
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  obtain ⟨lowered, body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedReturnLambdaBodySupport.of_return
    produced.site.code produced.recipe inputs frame ledger profile actualView rfl
    returnFound returnForm returnType childFound childType childTyped
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Syntax expression)
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Child expression lowered) body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩

/-- The nullary entry point keeps its original API. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda [] result [statement])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) :=
  of_terminal_parameters terminal prepared diagnostic wellFormed profile selected member
    found form owner requirements coercions ordinary read returnFound returnForm returnType

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedReturnLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion
/-! The actual typed contracted lambda already contains its original body's
native typing. Creation copies, snapshot, frame, manifest, per-call copies and
parameter wrappers are inverted through their literal accepted compiler
receipts. Only unused syntax binders
are removed. Source typing, body syntax, selected authority and execution are
independent; no expected body typing premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion
open Core Frontend SourceInference
open CallableIndexedLambdaValues

/-- Remove the one unused packed argument after the real parameter references.
The arbitrary prefix remains exact; this is static typing pullback only. -/
theorem remove_prefix_slot {definitions : DataEnvironment}
    (front suffix : Core.Context) (inserted : Ty) {expression : Expr} {result : Ty}
    (typed : HasType (front ++ inserted :: suffix)
      (expression.weakenAt front.length) result definitions) :
    HasType (front ++ suffix) expression result definitions := by
  have back : TypedLexicalWhile.Native.PullsBack (Renaming.insertion front.length)
      (front ++ suffix) (front ++ inserted :: suffix) := by
    clear typed
    induction front with
    | nil =>
      intro index type found
      simpa [Renaming.insertion] using found
    | cons first rest ih =>
      simpa only [List.length_cons, List.cons_append, Renaming.lift_insertion] using ih.lift first
  rw [← Expr.rename_insertion] at typed
  exact TypedLexicalWhile.Native.typing expression back typed

/-- The real manifest hook inserts only its metadata product. Acceptance
identifies that literal wrapper; its native let body gives the same allocation. -/
theorem manifest_body {checked : SourceCoreCompatibleCatalog.Checked}
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {node : ExpressionNode} {parameter result : Ty} {body emitted : Expr}
    (accepted : SourceCoreLambdaTemplates.hook inventory owner active compilation source scope node
      parameter result body = .ok emitted)
    {definitions : DataEnvironment} {context : Core.Context}
    (typed : HasType context emitted (LanguageResult.resultType result) definitions) :
    HasType context body (LanguageResult.resultType result) definitions := by
  simp only [SourceCoreLambdaTemplates.hook, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw] at accepted
  repeat' first | split at accepted | contradiction
  rename_i _ template selected metadata header _ fields fieldsAccepted _ checkedScope scopeChecks
  cases accepted
  cases typed with
  | letE metadataTyped bodyTyped =>
    exact TypedLexicalWhile.Native.remove_front bodyTyped

/-- A scope slot holds a cell of its payload type in the scope's own context. -/
private theorem scope_slot {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {index : Nat} {id : Resolved.LocalId} {payload : Ty} (found : scope[index]? = some (id, payload)) :
    (SourceCoreLocalCell.coreContext scope ++ administrative)[index]? = some (.cell (OptionalCell.cellType payload)) := by
  rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using (List.getElem?_eq_some_iff.mp found).1)]
  simp [SourceCoreLocalCell.coreContext, found]

/-- The contracted carrier fixes the literal anonymous snapshot lambda inside
its creation copies. The copies, the saved lexical frame and two frame
temporaries do not alter its original raw body code, so its typing follows
without a separately typed body input. -/
theorem raw_body {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) :
    HasType (code.receipt.parameterCore :: SourceCoreLocalCell.coreContext scope ++ administrative)
      code.receipt.rawBody (LanguageResult.resultType code.receipt.resultCore) prepared.layouts.definitions := by
  have snapshotted := code.typed
  rw [code.emitted] at snapshotted
  have typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code.expression
      (LanguageResult.resultType (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore))
      prepared.layouts.definitions := by
    have snapshot := code.receipt.snapshot
    rw [code.decorated] at snapshot
    split at snapshot
    · rw [code.allocationProfile] at snapshot
      exact CaptureCopyTyping.copyScopeIndexed_body_hasType snapshot
        (fun _ _ _ found => scope_slot found) snapshotted
    · rw [Except.ok.inj snapshot]
      exact snapshotted
  cases typed with
  | inRight _ wrapped =>
    cases wrapped with
    | pair tagged contract =>
      cases tagged with
      | pair identity snapshot =>
        cases snapshot with
        | letE saved lambda =>
          cases lambda with
          | lambda parameter result native =>
            have raw := CallableIndexedParameterNativeInversion.withFrame_body native
            exact TypedLexicalWhile.Native.remove_second raw

/-- The actual allocation receipt fixes every parameter reference. The real
packed argument is the sole unused slot removed after those references. The
returned native typing has exactly the Site's canonical source body scope. -/
theorem body_native {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code prepared function scope administrative) :
    HasType (SourceCoreLocalCell.coreContext
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      code.receipt.body (LanguageResult.resultType code.receipt.resultCore) prepared.layouts.definitions := by
  have copied := manifest_body (code.manifest ▸ code.receipt.bodyHook) (raw_body code)
  have allocated := CaptureCopyTyping.copyScopeIndexed_body_hasType
    (CallableIndexedLambdaEntryPrefix.copies_accepted (values := .initial checked) code)
    (fun _ _ _ found => by
      simp only [List.cons_append, List.getElem?_cons_succ]
      exact scope_slot found) copied
  have body := CallableIndexedParameterNativeInversion.accepted_body code.allocationError
    (CallableIndexedLambdaEntryPrefix.prefix_accepted (values := .initial checked) code) allocated
  rw [CallableIndexedParameterNativeInversion.final_context] at body
  let front := SourceCoreLocalCell.coreContext
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)))
  have length : front.length = code.receipt.loweredParameters.length := by
    simp [front, SourceCoreLocalCell.coreContext]
  have body := remove_prefix_slot
    front (SourceCoreLocalCell.coreContext scope ++ administrative) code.receipt.parameterCore
    (by simpa only [front, length, List.cons_append, List.append_assoc] using body)
  simpa only [front, SourceCoreLocalCell.coreContext, List.map_append, List.append_assoc] using body

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport
/-! The actual branching lambda callback builds a static body certificate.
Children retain their original typed nodes; application meaning is supplied
later by the recursive body family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)

def Syntax : TypedSource → ExpressionId → Prop := fun _ _ => True

def Child : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ source => CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate source
    (fun _ _ _ _ => True)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Every tree node is recovered from the accepted same-view compiler flow and
independent Source syntax at the real parameter context. -/
theorem of_branching
    (retained : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named code)
    {index : Nat} (selected : compiled.indexed.base.functions[index]? = some named)
    (source : function.source = CallableIndexedNamedGeneration.source named)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (sameCompilation : code.compilation = context compiled.indexed named)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (view : code.view = function.source)
    (owner : code.compilation.owner = named.signature.key)
    (active : code.active = [])
    (onError : code.allocationError = fun error => .sourceAllocation (reprStr error))
    (signatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (hidden : GenericImperativeMatch.MatchHiddenFresh function.source)
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) inputs.context)
    (shape : CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (Syntax function.source)
      inputs.context (.statements true function.body) function.resultType) :
    ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) Syntax Child code
      (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax function.source)
        body.context (.statements true function.body) function.resultType := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, issued, recipe, _policyRecipe, _sameCompilation⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    (congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe).trans
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
        compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
      code.compilation.internalReason code.compilation.internalReason := (Except.ok.inj returned).symm
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections code profile).2
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have generatedSource : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow := by
    simpa only [view] using generated
  have binderPolicy : ∀ current binder, binder.scheme.quantified = [] →
      policy.lowerBinder function.source current binder =
        SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked function.source current binder := by
    intro current binder mono
    change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
    simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
    rfl
  have allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt code.compilation.owner code.active code.allocationError)) := by
    rw [owner, active, onError]
    rfl
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy policy
      (.initial compiled.compatible.checked)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root operator => if operator = .equal then Word.zero else compilation.own.assignments.reasonAt site root (.value operator))
      (fun site root type => diagnostics.placeReason named.signature.key site root (some type)) := by
    refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl
  have unaryPolicy : CompatibleBitNotStatements.Policy policy (.initial compiled.compatible.checked)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root => compilation.own.assignments.reasonAt site root .bitNot)
      (fun site root type => diagnostics.placeReason named.signature.key site root (some type)) := rfl
  obtain ⟨first, assignmentPrepared⟩ :=
    CallableIndexedOwnedIssuedAssignmentRecipes.assignments_prepared selected compilation issued
  rw [← source] at assignmentPrepared
  have operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (if operator = .equal then Word.zero else compilation.own.assignments.reasonAt site assignment.target.root (.value operator)) := by
    intro site assignment operator rhs occurrence rawProfile
    exact PreparedBranchingAssignmentDiagnostics.operands assignmentPrepared
      (fun reason token represented => included reason token
        (CallableIndexedOwnedIssuedAssignmentRecipes.operands compilation issued receiver represented)) occurrence rawProfile
  have unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs function.source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot)
        (compilation.own.assignments.reasonAt site assignment.target.root .bitNot) := by
    intro site assignment origin rawWord
    exact GenericAssignmentUnaryDiagnostics.prepared_unary_included assignmentPrepared
      (fun reason token represented => included reason token
        (CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.compilation_unary compilation issued receiver represented))
      origin rawWord
  let baseMatch : SourceCoreCompatibleDataMatches.Context :=
    ⟨.initial compiled.compatible.checked, (context compiled.indexed named).solvedRequirements,
      some (allocator compiled.indexed named), none⟩
  have matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy
      (CompatibleMatchAmbientLowering.withDefinitions baseMatch compiled.indexed.layouts.definitions) := by
    apply CompatibleMatchAmbientLowering.PolicySuccess.extend (show policy.lowerMatch = some
      (SourceCoreCompatibleDataMatches.lowerWithReasons baseMatch) from rfl)
    exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩
  have matchAllocator : (CompatibleMatchAmbientLowering.withDefinitions baseMatch
      compiled.indexed.layouts.definitions).sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length
        (compiled.indexed.layouts.allocatorAt code.compilation.owner code.active code.allocationError)) := by
    rw [owner, active, onError]
    rfl
  have matchLedger : inputs.context.solvedRequirements = baseMatch.solvedRequirements := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).solvedRequirements.trans
      (sameLedger.trans (by rw [sameCompilation]))
  let collected : CallableIndexedOwnedPreparedBranchingCatalogSites.Collected
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw)) (faults := faults) compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) function.source (Syntax function.source) (Child 0 function.source)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow :=
    CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
      (CallableLambdaViewEdits.LocalView.refl function.source)
      (by intro id member; cases member)
      frame.code.graph.nodeOccurrencesUnique
      (show policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked from rfl)
      binderPolicy allocationPolicy assignments unaryPolicy operands unary
      matchPolicy rfl rfl matchAllocator hidden catalog matchLedger
      (certificates := fun _ _ _ _ => True)
      (by intros; exact True.intro)
      syntaxTree.prepared rfl shape.forget (Dynamic.RuntimeContextFields.refl _)
      runtime.variables_closed runtime.residual_variables_open signatures declarations
      (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩)) projection generatedSource native
  let full := collected.tree
  have sites : full.CatalogSites .reachable registry faults := PreparedBranchingLegacyCatalogSites.body (collected.sites registry) shape
  let actualTree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) code.view (Syntax code.view) (Child 0 code.view)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow := by
    simpa only [view] using full
  have actualSites : actualTree.CatalogSites .reachable registry faults := by
    simpa only [view] using sites
  refine ⟨{
    toContext := inputs, frame := frame, readFuel := 0, policy := policy, callback := callback
    flow := flow, generated := generated, projection := projection, emitted := emitted
    actualTree := actualTree, actualSites := actualSites, tree := full, sites := sites
    valid := CallableIndexedLambdaStaticBodySupport.context_valid (values := .initial compiled.compatible.checked) code inputs frame sameLedger
    unique := frame.code.graph.nodeOccurrencesUnique }, rfl, syntaxTree⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation
/-! Actual named compilation retains the same lambda and its complete
scoped imperative body. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (shape : CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape header.function.source true statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.Syntax header.function.source
        (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result statements header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  have entryDeclarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
    (values := .initial compiled.compatible.checked) produced.site.code inputs facts declarations
  have signatures : inputs.context.signatures = compiled.compatible.checked.signatures := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).signatures.trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
  have syntaxTree : GenericImperativeMatch.Syntax function.source
      (CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax function.source)
      inputs.context (.statements true function.body) function.resultType := by
    have typed : StatementsHaveType header.function.source {returnType := result}
        inputs.context statements _finalContext _bodyFacts := by
      simpa only [function, closure, source, ← header.agreement.source] using bodyTyped
    simpa only [function, closure, source, ← header.agreement.source] using syntaxFor typed
  obtain ⟨body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedBranchingLambdaBodySupport.of_branching
    produced.site.code produced.issuedRecipe
    (by rw [terminal.aligned.named]; exact terminal.prepared.selected) rfl receiver included
    produced.site.compilation inputs frame ledger profile actualView
    (by rw [produced.site.compilation]; rfl) produced.site.active produced.site.allocationError
    signatures (CallableIndexedOwnedLocalIdentityFreshness.match_hidden_fresh ownership)
    (CallableIndexedOwnedPublicSignatureCatalog.well_formed compiled wellFormed) entryDeclarations (by simpa only [function, closure, source, ← header.agreement.source] using shape) syntaxTree
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Syntax
    CallableIndexedOwnedPreparedBranchingLambdaBodySupport.Child body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedBranchingBodyLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
/-! Bounded admission reads original expression nodes and their metadata.
The native metadata scan covers the whole admitted grammar. Declaration calls
are excluded by the empty direct-site criterion, so their original coercion
and requirement rows remain available to a separate parent certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles (NativeMetadataFor SupportedForm)
open CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport (PrimitiveSource)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by
        intro item member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail item member⟩

/-- This recognizer constructs syntax from the original lookups. Its budget
bounds graph traversal; it has no runtime or semantic inventory input. -/
def expression? (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (GeneralSyntax source id (fun _ => False)))
  | 0, _ => none
  | fuel + 1, id =>
      match found : source.lookupExpression? id with
      | none => none
      | some node =>
          match form : node.form with
          | .reference _name (.local _binder) => some ⟨.leaf (.read found form)⟩
          | .reference name (.builtinBoolean value) => some ⟨.leaf (.literal found (form ▸ .bool name value))⟩
          | .literal literal => some ⟨.leaf (.literal found (form ▸ .word literal))⟩
          | .integerLiteral literal resolution => some ⟨.leaf (.literal found (form ▸ .integer literal resolution))⟩
          | .tuple [] => some ⟨.leaf (.literal found (form ▸ .unit))⟩
          | .group inner => do
              let ⟨child⟩ ← expression? source fuel inner
              pure ⟨.group found form child⟩
          | .conditional condition first second => do
              let ⟨test⟩ ← expression? source fuel condition
              let ⟨yes⟩ ← expression? source fuel first
              let ⟨no⟩ ← expression? source fuel second
              pure ⟨.conditional found form test yes no⟩
          | _ => none

private def PrimitiveForm (form : ExpressionForm) : Prop :=
  (∃ name resolution, form = .reference name resolution) ∨
  (∃ spelling resolution, form = .integerLiteral spelling resolution) ∨
  (∃ condition first second, form = .conditional condition first second)

private def primitiveNode? (node : SourceInference.Node) :
    Option (PLift (∀ expression, node = .expression expression → PrimitiveForm expression.form)) :=
  match node with
  | .statement _ => some ⟨by intro expression impossible; cases impossible⟩
  | .expression expression =>
      match form : expression.form with
      | .reference name resolution =>
          some ⟨by intro actual same; cases same; exact .inl ⟨name, resolution, form⟩⟩
      | .integerLiteral literal resolution =>
          some ⟨by intro actual same; cases same; exact .inr (.inl ⟨literal, resolution, form⟩)⟩
      | .conditional condition first second =>
          some ⟨by intro actual same; cases same; exact .inr (.inr ⟨condition, first, second, form⟩)⟩
      | _ => none

/-- The terminal-method profile is deliberately narrower than expression
admission: every original expression must be a reference, integer or conditional. -/
def primitiveSource? (source : TypedSource) : Option (PLift (PrimitiveSource source)) := do
  let ⟨all⟩ ← allProof? (fun node => ∀ expression, node = .expression expression →
    PrimitiveForm expression.form) primitiveNode? source.nodes
  pure ⟨by
    intro id node found
    exact all _ (lookupExpression?_sound found).1 node rfl⟩

def NativeMetadataTest {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) : Prop :=
  node.coercions = [] ∧
  prepared.base.locals.bindings.find? (fun binding => decide
    (binding.caller = (CallableIndexedNamedGeneration.context prepared named).owner ∧ binding.initializer = node.id)) = none ∧
  (match node.form with | .integerLiteral _ _ => True | _ => node.requirements = []) ∧
  (match node.form with | .call _ _ (.indirect metadata) => metadata.argumentCoercions = [] | _ => True) ∧
  (match node.form with
    | .reference _ (.local binder) => prepared.base.locals.bindings.any (fun binding => decide
        (binding.caller = (CallableIndexedNamedGeneration.context prepared named).owner ∧ binding.binder.id = binder)) = false
    | _ => True)

private instance nativeMetadataTestDecidable {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) :
    Decidable (NativeMetadataTest prepared named node) := by
  unfold NativeMetadataTest
  cases node.form <;> try infer_instance
  case reference name resolution => cases resolution <;> infer_instance
  case call callee ids resolution => cases resolution <;> infer_instance

private def relevantForm : ExpressionForm → Bool
  | .proxy _ | .reference _ (.local _) | .reference _ (.builtinBoolean _) | .literal _ | .integerLiteral _ _
    | .unary _ _ | .binary _ _ _ | .index _ _ | .conditional _ _ _ | .group _ | .tuple _
    | .constructor _ _ | .call _ _ (.builtinFunction _) | .call _ _ (.indirect _) => true
  | _ => false

private theorem relevant_of_supported {form : ExpressionForm}
    (supported : SupportedForm form)
    (noDirect : ∀ callee ids instantiation, form = .call callee ids (.declaration instantiation) → False) :
    relevantForm form = true := by
  cases supported with
  | literal atomic => cases atomic <;> rfl
  | direct callee ids instantiation => exact False.elim (noDirect callee ids instantiation rfl)
  | proxy | read | unary | binary | index | conditional | group | tuple | constructor | builtin | call => rfl

private def nativeNodeMetadata? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (node : SourceInference.Node) :
    Option (PLift (∀ expression, node = .expression expression →
      relevantForm expression.form = true → NativeMetadataTest prepared named expression)) :=
  match node with
  | .expression expression =>
      if relevant : relevantForm expression.form = true then
        if accepted : NativeMetadataTest prepared named expression then
          some ⟨by intro actual same _; cases same; exact accepted⟩
        else none
      else some ⟨by intro actual same supported; cases same; exact False.elim (relevant supported)⟩
  | .statement _ => some ⟨by intro expression impossible; cases impossible⟩

/-- Native metadata for the empty direct-site grammar. The scanner examines
all relevant nodes, including unused ones. Integer evidence is preserved;
no other admitted node may carry requirements or output coercions. -/
def nativeMetadata? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    Option (PLift (NativeMetadataFor prepared named source (fun _ => False))) := do
  let ⟨all⟩ ← allProof? (fun node => ∀ expression, node = .expression expression →
    relevantForm expression.form = true → NativeMetadataTest prepared named expression)
    (nativeNodeMetadata? prepared named) source.nodes
  have metadataAt : ∀ id, GeneralSyntax source id (fun _ => False) → ∀ node,
      source.lookupExpression? id = some node → NativeMetadataTest prepared named node := by
    intro id tree node found
    obtain ⟨original, originalFound, supported⟩ :=
      CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.syntax_node tree
    cases Option.some.inj (originalFound.symm.trans found)
    exact all _ (lookupExpression?_sound found).1 node rfl
      (relevant_of_supported supported (fun _ _ _ form => tree.direct_site found form))
  pure ⟨{
    requirements := by
      intro id tree node found
      have accepted := (metadataAt id tree node found).2.2.1
      cases form : node.form <;> simp only [form] at accepted
      all_goals try exact .inl accepted
      case integerLiteral literal resolution => exact .inr ⟨literal, resolution, rfl⟩
    coercions := fun id tree node found => (metadataAt id tree node found).1
    initializer := by
      intro id tree
      obtain ⟨node, found⟩ := GeneralSyntax.syntax_found tree
      have nodeId := (lookupExpression?_sound found).2
      simpa only [nodeId] using (metadataAt id tree node found).2.1
    arguments := by
      intro id tree node found callee ids metadata form
      simpa only [form] using (metadataAt id tree node found).2.2.2.1
    directCaller := by
      intro id tree node found callee ids instantiation form
      exact False.elim (tree.direct_site found form)
    localRead := by
      intro id tree node found name binder form
      simpa only [form] using (metadataAt id tree node found).2.2.2.2 }⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReachedNativeExpressionTreeBounds
/-! The actual compiler Tree is folded with native witnesses at each used
occurrence. One-level native inversion strengthens only the child positions
used by that original head. Its finite Entries may contain unused positions;
their native typing is never requested. A call leaf also retains its own raw
typing for the same accepted lambda/indirect compiler receipt.

The primitive, data, builtin and tuple branches use the original admitted
head producers. The remaining call dispatcher is explicitly restricted to the
three actual raw compiler alternatives and their used children. Its lambda,
named and indirect branches must be composed with the strict body induction;
no completed expression Tree or body execution law is an assumption here.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReachedNativeExpressionTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedExpressionNativeChildren (WithRaw)
open CallableIndexedOwnedPreparedNativeAssignmentChildren (RawTyped)

universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {compilerScope : SourceCoreLocalCell.Scope}
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (inventory : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))
  (administrative : Core.Context)

/-- Static raw typing at the literal occurrence context. It has no runtime
or Source typing conclusion. The arbitrary native result remains existential. -/
def NativeAt (certificate : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => certificate scope id lowered ∧
    RawTyped (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression compiled.indexed.layouts.definitions

private abbrev rawCalls : CompatibleExpressionCalls.CallHeads :=
  CallableIndexedOwnedPreparedRawCompilerHeads.Head root expressionSyntax callerEvidence inventory
    (sourceContext := sourceContext) (scope := compilerScope)

/-- Each call carries the same authentic static receipt and its own local raw
typing. In particular the zero-child lambda still retains parent typing. -/
abbrev NativeCalls (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  NativeAt (compiled := compiled) administrative (rawCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory children)

private def pointCertificate (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current expression code => current = scope ∧ expression = id ∧ code = lowered

/-- Only actual used child slots are strengthened by the same parent typing.
The additional call field is that parent witness, not a child/body law. -/
theorem native_head {children : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {nativeType : Ty}
    (head : CompatibleExpressionCalls.Head (rawCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory)
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt children scope id lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    CompatibleExpressionCalls.Head (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative)
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt
      (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative)
        compiled.indexed.layouts.definitions children) scope id lowered := by
  have actual := CallableIndexedOwnedPreparedExpressionNativeChildren.head_with_raw
    (fun actual _nativeType actualTyped =>
      CallableIndexedOwnedPreparedRawCompilerHeadNativeChildren.raw_children
        (sourceContext := sourceContext) (scope := compilerScope) root expressionSyntax callerEvidence inventory actual actualTyped) head typed
  cases actual with
  | primitive head => exact .primitive head
  | constructor receipt form valid sequence => exact .constructor receipt form valid sequence
  | member metadata baseMetadata form layout certified =>
      exact .member metadata baseMetadata form layout certified
  | index header keyFound form sourceType baseCertified keyCertified =>
      exact .index header keyFound form sourceType baseCertified keyCertified
  | builtin head => exact .builtin head
  | tuple receipt sequence => exact .tuple receipt sequence
  | call head => exact .call ⟨head, ⟨_, typed⟩⟩

variable {fuel : Nat} {solved : List SolvedRequirement} {literals : GenericExpressionMeaning.Certificate}

/-- The exact original Tree and literal receipts, together with its actual
root native witness. No typing is asserted for an unused Entries member. -/
abbrev NativeTree : GenericExpressionMeaning.Certificate :=
  NativeAt (compiled := compiled) administrative
    (CompatibleExpressionCalls.Tree.WithLiterals
      (calls := rawCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory) (fuel := fuel)
      (values := .initial compiled.compatible.checked) (source := source named)
      (context := sourceContext) (solved := solved) (reasonAt := rootReasonAt) literals)

/-- This induction follows the SAME LiteralSites proof and ordered Entries.
The one-level head inversion supplies a raw witness before selecting a child
IH. An unused child IH is never invoked. -/
private theorem fold_native
    (Meaning : Nat → GenericExpressionMeaning.Certificate → Prop)
    (select : ∀ {size certificate}, Meaning size certificate → ∀ {scope id lowered},
      certificate scope id lowered → Meaning size (pointCertificate scope id lowered))
    (gather : ∀ {size certificate},
      (∀ {scope id lowered}, certificate scope id lowered → Meaning size (pointCertificate scope id lowered)) →
      Meaning size certificate)
    (budget size : Nat) (within : size ≤ budget)
    (fragments : ∀ child, child ≤ budget → Meaning child
      (CompatibleExpressionBuiltins.Tree.WithLiterals (fuel := fuel) (values := .initial compiled.compatible.checked)
        (source := source named) (context := sourceContext) (solved := solved) (reasonAt := rootReasonAt) literals))
    (nodes : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → Meaning smaller
        (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries))) →
      Meaning child
        (CompatibleExpressionCalls.Head (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative)
          (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (source named) sourceContext rootReasonAt
          (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries)))) :
    Meaning size (NativeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
      (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative) := by
  apply gather
  intro scope id lowered supported
  obtain ⟨⟨tree, sites⟩, nativeType, typed⟩ := supported
  induction sites generalizing size nativeType with
  | fragment child childSites =>
      exact select (fragments size within) ⟨child, childSites⟩
  | @node id lowered entries head children childSites ih =>
      have meanings : ∀ smaller, smaller ≤ budget → Meaning smaller
          (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries)) := by
        intro smaller smallerWithin
        apply gather
        intro current expression code certified
        obtain ⟨⟨rfl, member⟩, childType, childTyped⟩ := certified
        exact ih expression code member (size := smaller) (nativeType := childType) smallerWithin childTyped
      exact select (nodes scope entries size within meanings)
        (native_head (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative head typed)

section Semantics
variable {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  (unique : NodeOccurrencesUnique (source named))
  (reads : ReachedLoweredReadOutcomePorts.ReadPolicies fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (source named) sourceContext rootReasonAt faults)
  (missing : IndexFaultPostContracts.MissingPolicies (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (source named) functions registry program sourceContext evidence rootReasonAt faults)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program sourceContext (source named))
  (covers : evidence.Covers sourceContext)

private abbrev P (certificate : GenericExpressionMeaning.Certificate) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt bridge
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    sourceContext evidence (source named) certificate faults size

private abbrev R (certificate : GenericExpressionMeaning.Certificate) (size : Nat) : Prop :=
  CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt bridge
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    sourceContext evidence (source named) certificate faults size

include transport extension faithful observations functionTypes unique reads missing wellFormed runtime covers in
/-- All non-call heads and exact builtin fragments are closed internally.
Only the actual raw lambda/named/indirect alternatives remain in callLeaves;
that dispatcher must consume the strict F induction at the retained body. -/
private theorem preserves_with_literals
    (literalMeaning : GenericExpressionMeaning.Preserves
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program sourceContext evidence (source named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (callLeaves : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries)) smaller) →
      P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative
          (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries))) child) :
    P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence (NativeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
      (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative) size := by
  apply fold_native (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative
    (fun size certificate => P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence certificate size)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt.of_stateful wellFormed runtime covers
      (ProtectedStateTransition.PreservesAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.preserves_at_of_unbounded
          (ProtectedExpressionMeaning.preserves_of_typed _
            (CallableIndexedOwnedReachedExpressionDiagnosticBounds.preserves_with_literals functions extension faithful observations functionTypes
              program evidence unique reads missing literalMeaning)) child))
  · intro scope entries child childWithin children
    exact CallableIndexedOwnedReachedAdmittedExpressionCallsHeads.preserves_at_with_calls
      bridge transport functions extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative) budget child childWithin children
      (callLeaves scope entries child childWithin children)

include transport extension faithful observations functionTypes unique reads missing wellFormed runtime covers in
/-- Reflection follows each actual Core grade; each head returns its own
independent Source grade and the same admitted reached witness. -/
private theorem reflects_with_literals
    (literalMeaning : GenericExpressionMeaning.Reflects
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program sourceContext evidence (source named) literals faults)
    (budget size : Nat) (within : size ≤ budget)
    (callLeaves : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries)) smaller) →
      R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative
          (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries))) child) :
    R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence (NativeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
      (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative) size := by
  apply fold_native (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) (literals := literals) root expressionSyntax callerEvidence inventory administrative
    (fun size certificate => R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence certificate size)
    (fun meaning _ _ _ certified _ _ _ point => by
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact meaning certified)
    (fun meanings scope id lowered certified => meanings certified ⟨rfl, rfl, rfl⟩)
    budget size within
  · intro child _within
    exact CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt.of_stateful wellFormed runtime covers
      (ProtectedStateTransition.ReflectsAt.of_administrative _ _ _ _ _ _ _ _ transport
        (RecursiveNamedBoundedContracts.reflects_at_of_unbounded
          (ProtectedExpressionMeaning.reflects_of_typed _
            (CallableIndexedOwnedReachedExpressionDiagnosticBounds.reflects_with_literals functions extension faithful observations functionTypes
              program evidence unique reads missing literalMeaning)) child))
  · intro scope entries child childWithin children
    exact CallableIndexedOwnedReachedAdmittedExpressionCallsHeads.reflects_at_with_calls
      bridge transport functions extension faithful observations functionTypes evidence unique missing wellFormed runtime covers
      (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative) budget child childWithin children
      (callLeaves scope entries child childWithin children)


/-- The actual runtime literal family retains only validator-selected rows of
this same compiler Tree. Its denotation is constructed from the real ledger. -/
abbrev RuntimeTree : GenericExpressionMeaning.Certificate :=
  NativeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
      (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative
    (literals := fun _ id lowered =>
      CompatibleExpressionLiteralRuntime.Certificate solved (source named) id lowered)

include transport extension faithful observations functionTypes unique reads missing wellFormed runtime covers in
/-- Actual runtime literal and non-call meanings are manufactured internally.
The remaining three call alternatives must use the strict body family. -/
theorem preserves_at (sameLedger : sourceContext.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid sourceContext)
    (budget size : Nat) (within : size ≤ budget)
    (callLeaves : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries)) smaller) →
      P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative
          (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries))) child) :
    P (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence (RuntimeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative) size :=
  preserves_with_literals (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative
    bridge transport functions extension faithful observations functionTypes evidence unique reads missing
    wellFormed runtime covers
    (CompatibleExpressionLiteralRuntime.preserves functions program sourceContext evidence
      sameLedger runtimeLedger unique faults) budget size within callLeaves

include transport extension faithful observations functionTypes unique reads missing wellFormed runtime covers in
/-- The same native Tree yields an independent Source grade and the actual
reached admission. No literal or completed-expression execution law is input. -/
theorem reflects_at (sameLedger : sourceContext.solvedRequirements = solved)
    (runtimeLedger : RuntimeRequirementLedgerValid sourceContext)
    (budget size : Nat) (within : size ≤ budget)
    (callLeaves : ∀ scope entries child, child ≤ budget →
      (∀ smaller, smaller ≤ budget → R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
          (CompatibleExpressionCalls.Entries scope entries)) smaller) →
      R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence
        (NativeCalls (sourceContext := sourceContext) (compilerScope := compilerScope) root expressionSyntax callerEvidence inventory administrative
          (WithRaw (SourceCoreLocalCell.coreContext scope ++ administrative) compiled.indexed.layouts.definitions
            (CompatibleExpressionCalls.Entries scope entries))) child) :
    R (named := named) (sourceContext := sourceContext) (registry := registry) (faults := faults) bridge functions evidence (RuntimeTree (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative) size :=
  reflects_with_literals (sourceContext := sourceContext) (compilerScope := compilerScope)
    (fuel := fuel) (solved := solved) root expressionSyntax callerEvidence inventory administrative
    bridge transport functions extension faithful observations functionTypes evidence unique reads missing
    wellFormed runtime covers
    (CompatibleExpressionLiteralRuntime.reflects functions program sourceContext evidence
      sameLedger runtimeLedger (source named) faults) budget size within callLeaves

end Semantics
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReachedNativeExpressionTreeBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedDiagnosticSources
/-! The finite Header factory retains its selected diagnostic issuer. Transport
that actual preparation to the Header's literal owner and Source, then derive
the assignment table and every structural token equation from the same receipt.
No independent diagnostic identity or body execution law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedDiagnosticSources
open Core Frontend SourceInference
open RecursiveNamedPublicSpecializationMeaning
open RecursiveNamedPreparedHeaderPolicies
open CallableIndexedOwnedPreparedFiniteNamedInventories
open CallableIndexedOwnedContextualLambdaSourceDiagnostics (IssuedSource)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (receipt : Issued input)

/-- This is the freshly selected second pass used by the actual Header. -/
def prepared : Prepared compiled input.row :=
  CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared receipt.selected

theorem source : receipt.header.function.source = CallableIndexedNamedGeneration.source input.prepared.named := by
  rw [receipt.function]
  rfl

/-- Preserve the complete original preparation, including its first token,
inventory and typed Source. Only the owner and Source indices are transported. -/
def issuer : IssuedSource compiled receipt.header.owner receipt.header.function.source where
  first := receipt.selected.issued.first
  assignments := receipt.selected.issued.assignments
  assignmentsPrepared := by rw [source receipt]; exact receipt.selected.issued.assignmentsPrepared
  typing := by rw [source receipt]; exact receipt.selected.issued.typing
  plan := receipt.selected.issued.plan
  root := receipt.selected.issued.root
  extra := receipt.selected.issued.extra
  diagnostics := receipt.selected.issued.diagnostics
  prepared := receipt.selected.issued.prepared
  collected := by rw [receipt.aligned.owner, source receipt]; exact receipt.selected.issued.collected

theorem assignments : (issuer receipt).assignments = (prepared receipt).compilation.own.assignments :=
  receipt.selected.assignments

theorem assignments_prepared : SourceCoreAssignmentFaultSites.prepare receipt.header.function.source
    (issuer receipt).first = .ok (prepared receipt).compilation.own.assignments := by
  rw [← assignments receipt]
  exact (issuer receipt).assignmentsPrepared

theorem operand : (issuer receipt).invalidOperand = Prepared.invalidOperand (prepared receipt) := by
  funext site root operator
  simp only [IssuedSource.invalidOperand, Prepared.invalidOperand, GenericAssignmentDiagnostics.token,
    assignments receipt]

theorem unary : (issuer receipt).invalidUnary = Prepared.invalidUnary (prepared receipt) := by
  funext site root
  simp only [IssuedSource.invalidUnary, Prepared.invalidUnary, assignments receipt]

theorem projection : (issuer receipt).invalidProjection = Prepared.invalidProjection (prepared receipt) := by
  funext site root
  change receipt.selected.issued.diagnostics.program.placeReason receipt.header.owner site root none =
    (CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.lowered compiled receipt.selected.diagnostics).placeReason
      input.prepared.named.signature.key site root none
  rw [receipt.aligned.owner]
  exact receipt.selected.places _ _ _ _

theorem missing : (issuer receipt).missingDefault = Prepared.missingDefault (prepared receipt) := by
  funext site root valueType
  change receipt.selected.issued.diagnostics.program.placeReason receipt.header.owner site root (some valueType) =
    (CallableIndexedOwnedSelectedDiagnosticIssuerReceipts.lowered compiled receipt.selected.diagnostics).placeReason
      input.prepared.named.signature.key site root (some valueType)
  rw [receipt.aligned.owner]
  exact receipt.selected.places _ _ _ _

/-- The receiving typed assignment factory comes from the retained issuer,
with the exact selected table; it does not demand another diagnostic receipt. -/
def factory : AssignmentDiagnosticOrigins.Factory true .reachable receipt.header.function.source
    (issuer receipt).invalidOperand :=
  AssignmentDiagnosticOrigins.Factory.prepared (issuer receipt).typing.2 (issuer receipt).assignmentsPrepared

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedDiagnosticSources
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedImperativeLambdaBodySupport
/-! The actual bare-assignment lambda callback builds a static body certificate.
Children retain their original typed nodes; application meaning is supplied
later by the recursive body family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedImperativeLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)

def Syntax : TypedSource → ExpressionId → Prop := fun _ _ => True

def Child : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ source => CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate source
    (fun _ _ _ _ => True)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Every tree node is recovered from the accepted same-view compiler flow and
independent Source syntax at the real parameter context. -/
theorem of_imperative
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (view : code.view = function.source)
    (owner : code.compilation.owner = named.signature.key)
    (active : code.active = [])
    (onError : code.allocationError = fun error => .sourceAllocation (reprStr error))
    (signatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) inputs.context)
    (shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape function.source function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (Syntax function.source)
      inputs.context (.statements true function.body) function.resultType) :
    ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) Syntax Child code
      (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax function.source)
        body.context (.statements true function.body) function.resultType := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    (congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe).trans
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
        compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
      code.compilation.internalReason code.compilation.internalReason := (Except.ok.inj returned).symm
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections code profile).2
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have generatedSource : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow := by
    simpa only [view] using generated
  have binderPolicy : ∀ current binder, binder.scheme.quantified = [] →
      policy.lowerBinder function.source current binder =
        SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked function.source current binder := by
    intro current binder mono
    change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
    simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
    rfl
  have allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt code.compilation.owner code.active code.allocationError)) := by
    rw [owner, active, onError]
    rfl
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy policy
      (.initial compiled.compatible.checked)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root operator => if operator = .equal then Word.zero else compilation.own.assignments.reasonAt site root (.value operator))
      (fun site root type => diagnostics.placeReason named.signature.key site root (some type)) := by
    refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl
  let full : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) function.source (Syntax function.source) (Child 0 function.source)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow :=
    CallableIndexedOwnedPreparedNativeBareImperativeCollectors.tree
      (CallableLambdaViewEdits.LocalView.refl function.source)
      (by intro id member; cases member)
      frame.code.graph.nodeOccurrencesUnique
      (show policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked from rfl)
      binderPolicy allocationPolicy assignments
      (certificates := fun _ _ _ _ => True)
      (by intros; exact True.intro)
      syntaxTree rfl shape (Dynamic.RuntimeContextFields.refl _)
      runtime.variables_closed runtime.residual_variables_open signatures declarations
      (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩)) projection generatedSource native
  have sites : full.CatalogSites .reachable registry faults :=
    CallableIndexedOwnedPreparedBareAssignmentCatalogSites.sites full rfl shape
  let actualTree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) code.view (Syntax code.view) (Child 0 code.view)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow := by
    simpa only [view] using full
  have actualSites : actualTree.CatalogSites .reachable registry faults := by
    simpa only [view] using sites
  refine ⟨{
    toContext := inputs, frame := frame, readFuel := 0, policy := policy, callback := callback
    flow := flow, generated := generated, projection := projection, emitted := emitted
    actualTree := actualTree, actualSites := actualSites, tree := full, sites := sites
    valid := CallableIndexedLambdaStaticBodySupport.context_valid (values := .initial compiled.compatible.checked) code inputs frame sameLedger
    unique := frame.code.graph.nodeOccurrencesUnique }, rfl, syntaxTree⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedImperativeLambdaBodySupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEmptyLambdaFormation
/-! Actual named terminal lowering constructs an empty ordinary lambda's
formation receipt. Source typing comes from the accepted Header, native typing
from the same checked cached body, and both trees from the literal empty body. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEmptyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

private theorem native_child
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) (emptyInputs : entry.native.inputTypes = []) :
    HasType (SourceCoreLocalCell.coreContext
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.receipt.child.expression (LanguageResult.resultType terminal.receipt.child.type)
      compiled.indexed.layouts.definitions := by
  have cached := terminal.prepared.cached.trans (congrArg some terminal.prepared.compilation.emitted)
  have cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code) := by
    simpa only [terminal.aligned.slot, terminal.aligned.named, terminal.aligned.code] using cached
  have typed := RecursiveNamedCatalogNativeContexts.prepared_body compiled.indexedPrepared member
    (values := .initial compiled.compatible.checked)
    (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) rfl header cached
    (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)
  have child := terminal.receipt.native_child_exact typed
  change HasType _ _ _ compiled.indexed.layouts.definitions at child
  simpa only [RecursiveNamedCatalogNativeContexts.bodyPrefix, RecursiveNamedCatalogNativeContexts.bodyScope,
    RecursiveNamedLambdaFormationHeads.nativePrefix, emptyInputs, SourceCoreGeneralEntry.nativeInputContext,
    List.map_nil, List.reverse_nil, List.append_nil, List.append_assoc,
    CallableIndexedAmbient.ambient_definitions, ← header.parameterType] using child

/-- All shape checks refer to the original, actually lowered occurrence. -/
theorem of_terminal
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries) (emptyInputs : entry.native.inputTypes = [])
    {node : ExpressionNode} {reported : Ty}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda [] .unit [])
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported)) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  have accepted := terminal.receipt.generated
  have expressionPolicy : header.policy.lowerExpression =
      (RecursiveNamedPreparedHeaders.Prepared.policy terminal.prepared).lowerExpression :=
    congrArg SourceCoreLoops.Policy.lowerExpression terminal.aligned.policy
  rw [expressionPolicy] at accepted
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext terminal.prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    terminal.prepared.compilation.parents terminal.prepared.compilation.own.assignments terminal.prepared.diagnostics
    (context compiled.indexed terminal.prepared.named) compiled.indexed.base.callableContext none none
    terminal.receipt.childFuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) terminal.expression header.reasonAt =
      .ok terminal.receipt.child at accepted
  have nonzero : terminal.receipt.childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have sourceEq : header.function.source = source terminal.prepared.named :=
    header.agreement.source.trans (congrArg source terminal.aligned.named)
  have record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      terminal.prepared.named.signature.key = .ok terminal.prepared.named.specialized := by
    simpa only [terminal.aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record compiled header
  obtain ⟨rawProduced⟩ := CallableIndexedOwnedContextualLambdaProducerReceipts.of_contextual
    terminal.prepared.compilation
    (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared terminal.prepared diagnostic) record header.context header.function.evidence profile
    (by rw [← sourceEq]; exact LambdaMetadataViews.MetadataView.refl _)
    (by simpa only [← sourceEq] using found) form found rfl owner requirements coercions ordinary read
    (by simpa only [fuelEq] using accepted) (native_child terminal member emptyInputs)
  have produced : Produced (compiled := compiled) header.named [] .unit [] header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      terminal.expression terminal.receipt.child := by
    simpa only [terminal.aligned.named] using rawProduced
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named [] .unit [] header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have parametersEmpty : produced.site.code.receipt.loweredParameters = [] := by
    have same := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) produced.site.code
    exact List.map_eq_nil_iff.mp same.symm
  let inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) produced.site.code := {
    context := header.context
    types := []
    extended := .nil _
    kinds := by simp only [parametersEmpty, List.not_mem_nil, false_implies, implies_true]
    referenceIndex := by
      change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
      rw [produced.site.compilation]
      rfl }
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  obtain ⟨body, _sameInputs⟩ := CallableIndexedOwnedPreparedEmptyLambdaBodySupport.of_empty produced.site.code
    (expressionSyntax := fun _ _ => False) (certificates := fun _ _ _ _ _ _ => False)
    produced.recipe inputs frame ledger profile rfl rfl
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    (fun _ _ => False) (fun _ _ _ _ _ _ => False) body
    (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_empty rfl)
    (CallableIndexedOwnedContextualLambdaProvenance.BodyReasons.of_empty rfl)
    declarations
    (.body (.nil (.inr rfl))) facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEmptyLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedImperativeBodyLambdaFormation
/-! Actual named compilation retains the same lambda and its complete
straight-line assignment body. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedImperativeBodyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (shape : CallableIndexedOwnedPreparedStagedBareAssignmentTree.Shape header.function.source statements)
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericImperativeMatch.Syntax header.function.source
        (CallableIndexedOwnedPreparedImperativeLambdaBodySupport.Syntax header.function.source)
        context (.statements true statements) result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result statements header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  have entryDeclarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
    (values := .initial compiled.compatible.checked) produced.site.code inputs facts declarations
  have signatures : inputs.context.signatures = compiled.compatible.checked.signatures := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).signatures.trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
  have syntaxTree : GenericImperativeMatch.Syntax function.source
      (CallableIndexedOwnedPreparedImperativeLambdaBodySupport.Syntax function.source)
      inputs.context (.statements true function.body) function.resultType := by
    have typed : StatementsHaveType header.function.source {returnType := result}
        inputs.context statements _finalContext _bodyFacts := by
      simpa only [function, closure, source, ← header.agreement.source] using bodyTyped
    simpa only [function, closure, source, ← header.agreement.source] using syntaxFor typed
  obtain ⟨body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedImperativeLambdaBodySupport.of_imperative
    produced.site.code produced.recipe inputs frame ledger profile actualView
    (by rw [produced.site.compilation]; rfl) produced.site.active produced.site.allocationError
    signatures entryDeclarations (by simpa only [function, closure, source, ← header.agreement.source] using shape) syntaxTree
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    CallableIndexedOwnedPreparedImperativeLambdaBodySupport.Syntax
    CallableIndexedOwnedPreparedImperativeLambdaBodySupport.Child body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedImperativeBodyLambdaFormation
end
