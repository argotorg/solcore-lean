import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaFormation

/-! Original named compiler children can combine general calls with closure
formation after lexical allocation. Both alternatives retain the accepted
callback, original typing and actual context; runtime captures come from entry. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Finite observations identify the original ordinary lambda occurrence and
its single return statement. The returned expression is checked separately by
the same retained closure family when the resulting handle is invoked. -/
structure ReturnLambda (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (id : ExpressionId) where
  node : ExpressionNode
  reported : Ty
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statement : StatementId
  returnNode : StatementNode
  expression : ExpressionId
  found : header.function.source.lookupExpression? id = some node
  form : node.form = .lambda parameters result [statement]
  owner : id.occurrence.owner = header.function.source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed header.named).owner ∧
      binding.initializer = id)) = none
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
    header.function.source id = .ok (node, reported)
  returnFound : header.function.source.lookupStatement? statement = some returnNode
  returnForm : returnNode.form = .returnStmt (some expression)
  returnType : returnNode.type = result

/-- Container observations are original node facts. The actual root policy
remains selected once while its recursive children use their smaller budgets. -/
structure Container (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (id : ExpressionId) where
  node : ExpressionNode
  found : header.function.source.lookupExpression? id = some node
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed header.named).owner ∧
      binding.initializer = id)) = none

inductive Syntax (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : ExpressionId → Prop where
  | general {id} (tree : GeneralSyntax header.function.source id) : Syntax header id
  | formation {id} (shape : ReturnLambda header id) : Syntax header id
  | group {id inner} (shape : Container header id) (form : shape.node.form = .group inner)
      (child : Syntax header inner) : Syntax header id
  | tuple {id ids} (shape : Container header id) (form : shape.node.form = .tuple ids)
      (children : ∀ child, child ∈ ids → Syntax header child) : Syntax header id

private theorem container_policy
    {named : CallableIndexedNamedGeneration.Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      named diagnostics namedCode compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : (∃ inner, node.form = .group inner) ∨ ∃ ids, node.form = .tuple ids)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
        binding.initializer = id)) = none) :
    CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root source scope id reasonAt := by
  rcases form with ⟨inner, form⟩ | ⟨ids, form⟩
  all_goals
    have sameSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
        (CallableIndexedNamedGeneration.context compiled.indexed named).plan compiled.indexed.base.locals
        (CallableIndexedNamedGeneration.context compiled.indexed named).owner none source id = .ok source := by
      simp [SourceCoreGeneralFunctions.contextualSource, found, form]
    constructor
    · rw [root.selected.readExpression]
      simp only [sameSource, bind, Except.bind]
      rw [CallableIndexedOwnedIndirectCompilerPolicyInputs.representation_read]
    · intro child budget
      rw [root.selected.special_eq, root.selected.special_body]
      have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
        unfold SourceCompilationPlan.ordinaryOwnedRequirements?
        rw [requirements, coercions]
        rfl
      have noEvidence : SourceCoreEvidence.lowerWithProjector compiled.indexed.base.sourceProgram
          ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key []).expressions.projectType
          named.specialized (CallableIndexedNamedGeneration.context compiled.indexed named)
          child budget source scope id reasonAt
          (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) = .ok none := by
        simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions]
      simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary,
        Option.filter_none, noEvidence, form]

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem child_certificates
    {source : TypedSource} {context : SourceSemantics.Context}
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {budget : Nat}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    {nativeContext : Core.Context} {definitions : DataEnvironment}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body budget
      compilation source scope id reasonAt) = .ok codes)
    (native : ∀ code, code ∈ codes → ∃ type, HasType nativeContext code.expression type definitions)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code →
      (∃ type, HasType nativeContext code.expression type definitions) → certificate id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      ∀ id code, (id, code) ∈ ids.zip codes → certificate id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first (native code (by simp))
      obtain ⟨count, nodes, children⟩ := ih tail rest
        (fun child member => native child (by simp [member]))
        (fun child member => extract child (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_⟩
      intro other otherCode member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact child
      · exact children other otherCode remaining

variable {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)


include aligned in
private theorem of_policy
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed prepared.named header.function.source)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {child : Staging.Recursive.Scope}
    (selected : (RecursiveNamedPreparedStageScopes.registry actual).Closure header.function child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields header.context context)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source scope context)
    {id : ExpressionId} (approved : Syntax header id)
    {node : ExpressionNode}
    (found : header.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType header.function.source context id node.type)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      prepared.named prepared.diagnostics prepared.code prepared.compilation rootFuel
      rootSource rootScope rootId rootReasonAt rootLowered)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody fuel
      (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (native : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.Certificate
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header bodyRegistry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context child.source := by
    rw [sameSource]
    exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)).transport fields
  have covers : child.evidence.Covers context := by
    rw [(RecursiveNamedPreparedStageScopes.registry actual).evidence selected]
    exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended)
  induction approved generalizing node fuel lowered nativeType with
  | general tree =>
    obtain ⟨actualRoot, samePrefix⟩ := CallableIndexedOwnedPreparedStagedNamedCanonicalScopedRoots.of_policy
      prepared aligned diagnostic receiver wellFormed metadata rows complete actual selected fields
      (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using tree)
      (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed) root
      (by simpa only [sameSource] using accepted)
    exact .canonical actualRoot samePrefix
  | formation shape =>
    have sameNode : node = shape.node := Option.some.inj (found.symm.trans shape.found)
    subst node
    obtain ⟨formation⟩ := CallableIndexedOwnedPreparedNamedSamePolicyLambdaFormation.of_expression
      prepared aligned root diagnostic wellFormed profile selected found shape.form shape.owner
      shape.requirements shape.coercions
      (by simpa only [aligned.named] using shape.ordinary) shape.read
      shape.returnFound shape.returnForm shape.returnType fields declarations typed accepted native
    exact .legacy (.formation formation runtime covers)
  | group shape form _child ih =>
    have sameNode : node = shape.node := Option.some.inj (found.symm.trans shape.found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have pointwise := container_policy root (scope := scope) (reasonAt := header.reasonAt)
        found (.inl ⟨_, form⟩) shape.requirements shape.coercions
        (by simpa only [aligned.named] using shape.ordinary)
      have step := CompatibleExpressionConditionals.step_of_functions (values := .initial compiled.compatible.checked) found (by rw [form]; constructor)
        pointwise.special pointwise.read accepted
      cases step with
      | group otherForm actualMetadata generated =>
        cases ExpressionForm.group.inj (form.symm.trans otherForm)
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types header.unique found form actualMetadata.coercions typed
        exact .group (by simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using actualMetadata) form
          (by simpa only [sameSource] using innerFound) sourceType
          (ih innerFound childTyped generated native)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | tuple shape form children ih =>
    have sameNode : node = shape.node := Option.some.inj (found.symm.trans shape.found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have pointwise := container_policy root (scope := scope) (reasonAt := header.reasonAt)
        found (.inr ⟨_, form⟩) shape.requirements shape.coercions
        (by simpa only [aligned.named] using shape.ordinary)
      obtain ⟨codes, generated, rfl, actualMetadata⟩ := CompatibleExpressionTuples.of_functions
        found form pointwise.special pointwise.read root.compilerPolicy.leafLowerer accepted
      obtain ⟨types, childTyped, sourceType⟩ := CompatibleExpressionTuples.source_types
        header.unique found form actualMetadata.coercions typed
      obtain ⟨count, nodes, certified⟩ := child_certificates header.unique childTyped generated
        (CallableIndexedOwnedPreparedNativeAssignmentChildren.packed_children native)
        (fun child member childNode code childFound childTyped childAccepted childNative => by
          obtain ⟨type, typed⟩ := childNative
          exact ih child member childFound childTyped childAccepted typed)
      refine .tuple runtime covers ⟨?_, form, sourceType⟩
        (CompatibleExpressionConstructors.sequence_of_nodes count
          (by simpa only [sameSource] using nodes)
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified
      simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using actualMetadata

include aligned in
/-- The complete inventory and original compiler observations construct both
canonical call children and ordinary formation at every actual lexical scope. -/
def of_actual
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed prepared.named header.function.source)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (Syntax header)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors.of_imperative_compiler
    prepared aligned ready wellFormed complete zero member receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic prepared aligned diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic prepared aligned diagnostic receiver)
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  obtain ⟨predecessor, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.policy_receipt
    prepared aligned accepted
  exact of_policy prepared aligned diagnostic receiver wellFormed profile metadata rows complete actual selected
    fields declarations approved found typed root root.selected.accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
