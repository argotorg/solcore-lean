import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalCompilerChildren
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerHeads

/-! A finite raw compiler skeleton retains each accepted lambda or indirect
call before native body collection. The actual Named compilation and selected
caller evidence remain explicit. No lambda Site, native typing, JointBody,
completed Tree or semantic execution law is required by the producer. A later
refinement must use this same Tree and these same accepted compiler receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedPreparedPrincipalCompilerChildren
open CallableIndexedOwnedPreparedMixedCompilerHeads (extraForm extraChildren)
open RecursiveNamedExpressionCompilerCertificates
open RecursiveNamedCallSelectionCertificates CallableAncestryPairedLookup

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {readFuel : Nat}
  (callerEvidence : Option Dynamic.EvidenceEnvironment)
  (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram))

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The same actual Named compiler owns both indirect actions. -/
structure IndirectReceipt (fuel : Nat) (id callee : ExpressionId) (ids : List ExpressionId)
    (metadata : IndirectCallResolution) (lowered : SourceCoreBasic.LoweredExpr) where
  compiler : CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody fuel
    (context compiled.indexed named) (source named) scope id callee ids metadata rootReasonAt lowered
  prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler compiled.indexed.ancestry.graph.inputs.callable
  sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler
  parentMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named)
    id compiler.original compiler.type
  positions : compiler.entries.map Prod.fst = callee :: ids
  physicalCount : ids.length = compiler.codes.length
  generated : ∀ child code, (child, code) ∈ compiler.entries → ∃ childNode,
    (source named).lookupExpression? child = some childNode ∧
    ExpressionHasType (source named) sourceContext child childNode.type ∧
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed named) (source named) scope child rootReasonAt = .ok code

/-- Raw lambda leaves retain the literal accepted compiler action and its
Source read/type metadata. Indirect leaves retain their actual ordered actions.
The selected named evidence remains the same explicit inventory alternative. -/
inductive Head (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate where
  | named {childScope id lowered}
      (head : RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers
        (context compiled.indexed named) (source named) sourceContext children childScope id lowered) :
      Head children childScope id lowered
  | lambda {childFuel id lowered node parameters result statements reported}
      (allowed : expressionSyntax (source named) id)
      (found : (source named).lookupExpression? id = some node)
      (form : node.form = .lambda parameters result statements)
      (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed named) (source named) scope id node parameters result statements
        reported rootReasonAt lowered)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
        (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered)
      (typed : ExpressionHasType (source named) sourceContext id node.type)
      (metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named) id node lowered.type) :
      Head children scope id lowered
  | indirect {childFuel id lowered node callee ids metadata}
      (found : (source named).lookupExpression? id = some node)
      (form : node.form = .call callee ids (.indirect metadata))
      (receipt : IndirectReceipt root (sourceContext := sourceContext) (scope := scope)
        childFuel id callee ids metadata lowered)
      (ordered : ∀ child code, (child, code) ∈ receipt.compiler.entries → children scope child code) :
      Head children scope id lowered

theorem include_named {children childScope id lowered}
    (head : RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers
      (context compiled.indexed named) (source named) sourceContext children childScope id lowered) :
    Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
      children childScope id lowered := .named head

theorem projected {children childScope id lowered node}
    (head : Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
      children childScope id lowered)
    (found : (source named).lookupExpression? id = some node) :
    compiled.compatible.checked.catalog.project node.type = .ok lowered.type := by
  cases head with
  | named actual =>
      cases callerEvidence with
      | none =>
          cases actual with
          | named _ metadata _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
              have same := Option.some.inj (metadata.found.symm.trans found)
              exact same ▸ metadata.projected
      | some evidence => exact RecursiveNamedCallEvidenceHeads.projected actual found
  | lambda _ actualFound _ _ _ _ metadata =>
      have same := Option.some.inj (actualFound.symm.trans found)
      exact same ▸ metadata.projected
  | indirect _ _ receipt _ =>
      have same := Option.some.inj (receipt.compiler.found.symm.trans found)
      have emitted := congrArg SourceCoreBasic.LoweredExpr.type receipt.compiler.output
      simpa only [same, emitted] using receipt.parentMetadata.projected

/-- Finite syntax, selected declaration and original policy obligations remain
static. No field requests a native child witness or a finished call Tree. -/
structure Domain : Prop where
  admission : AdmissionWith extraForm extraChildren (source named) (expressionSyntax (source named))
  coverage : ReachedCoverage headers (context compiled.indexed named) (source named)
    (expressionSyntax (source named))
  sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers sourceContext
  emptyEvidence : SelectedEmptyEvidence headers (context compiled.indexed named) (source named)
    (expressionSyntax (source named))
  order : ∀ id callee arguments instantiation node, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → node.form = .call callee arguments (.declaration instantiation) →
    Ordered (context compiled.indexed named).plan instantiation
  constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source named) sourceContext
    (expressionSyntax (source named))
  fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source named) sourceContext
    (CompatibleExpressionBuiltins.Syntax (source named))
  selectedValid : SelectedDeclarationLaw headers (context compiled.indexed named) (source named)
    sourceContext (expressionSyntax (source named))
  basePolicy : PolicyForWith (headers := headers) callerEvidence root.selected.policy
    (context compiled.indexed named) readFuel (.initial compiled.compatible.checked)
    (source named) sourceContext scope rootReasonAt
    (CallableIndexedOwnedPreparedMixedCompilerCertificates.baseAdmitted
      (source named) (expressionSyntax (source named)))
  fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax (source named) id →
    (source named).lookupExpression? id = some node → node.coercions = []
  coercions : ∀ id node, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → node.coercions = []
  empty : ∀ id node, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → extraForm node.form → node.requirements = [] ∧ node.coercions = []
  ordinary : ∀ id node, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → extraForm node.form →
    compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none
  arguments : ∀ id node callee ids metadata, expressionSyntax (source named) id →
    (source named).lookupExpression? id = some node → node.form = .call callee ids (.indirect metadata) →
    metadata.argumentCoercions = []

private theorem extra_cases {form : ExpressionForm} (extra : extraForm form) :
    (∃ parameters result statements, form = .lambda parameters result statements) ∨
      ∃ callee ids metadata, form = .call callee ids (.indirect metadata) := by
  cases form <;> simp only [extraForm] at extra
  case lambda parameters result statements => exact .inl ⟨parameters, result, statements, rfl⟩
  case call callee ids resolution =>
    cases resolution <;> simp only at extra
    case indirect metadata => exact .inr ⟨callee, ids, metadata, rfl⟩

private theorem pointwise_extra
    (domain : Domain root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope) (readFuel := readFuel))
    {id : ExpressionId} {node : ExpressionNode} (allowed : expressionSyntax (source named) id)
    (found : (source named).lookupExpression? id = some node) (extra : extraForm node.form) :
    PointwiseFor root (source named) scope id rootReasonAt := by
  obtain ⟨requirements, coercions⟩ := domain.empty id node allowed found extra
  have ordinary := domain.ordinary id node allowed found extra
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, metadata, form⟩
  · exact lambda_policy root found form requirements coercions ordinary
  · exact indirect_policy root found form requirements coercions (domain.arguments id node callee ids metadata allowed found form) ordinary

theorem policy_for_all
    (domain : Domain root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope) (readFuel := readFuel)) :
    PolicyForWith (headers := headers) callerEvidence root.selected.policy
      (context compiled.indexed named) readFuel (.initial compiled.compatible.checked)
      (source named) sourceContext scope rootReasonAt (expressionSyntax (source named)) where
  fragment := domain.basePolicy.fragment
  route := by
    intro id node allowed found
    by_cases extra : extraForm node.form
    · exact .inl (pointwise_extra root expressionSyntax callerEvidence headers domain allowed found extra).special
    · exact domain.basePolicy.route id node ⟨allowed, node, found, extra⟩ found
  read := by
    intro id allowed
    obtain ⟨node, found⟩ := domain.admission.base.found id allowed
    by_cases extra : extraForm node.form
    · exact (pointwise_extra root expressionSyntax callerEvidence headers domain allowed found extra).read
    · exact domain.basePolicy.read id ⟨allowed, node, found, extra⟩

private theorem accepted_read {childFuel : Nat} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (found : (source named).lookupExpression? id = some node)
    (extra : extraForm node.form)
    (pointwise : PointwiseFor root (source named) scope id rootReasonAt)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered) :
    ∃ actual reported, root.selected.policy.readExpression (source named) id = .ok (actual, reported) := by
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, metadata, form⟩
  all_goals
    rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    by_cases owner : id.occurrence.owner = (source named).owner
    · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, form, bind, Except.bind, pure, Except.pure] at accepted
      have bypass := pointwise.special (fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
          (min budget childFuel) (context compiled.indexed named) childSource childScope childId childReasonAt) (childFuel + 1)
      cases hook : root.selected.policy.lowerSpecial? <;> simp only [hook] at accepted bypass
      all_goals try rw [bypass] at accepted
      all_goals
        obtain ⟨pair, read, _⟩ := bind_ok accepted
        exact ⟨pair.1, pair.2, read⟩
    · simp [owner, bind, Except.bind] at accepted

private theorem row_length {source : TypedSource} {current : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source current ids types) : ids.length = types.length := by
  induction ids generalizing types with
  | nil => cases typed; rfl
  | cons head tail ih =>
      cases typed with
      | cons _ rest => exact congrArg Nat.succ (ih rest)

private theorem row_member {source : TypedSource} {current : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source current ids types) {id : ExpressionId} (member : id ∈ ids) :
    ∃ type, ExpressionHasType source current id type := by
  induction ids generalizing types with
  | nil => cases member
  | cons head tail ih =>
      cases typed with
      | cons headTyped tailTyped =>
          rcases List.mem_cons.mp member with same | remaining
          · subst id; exact ⟨_, headTyped⟩
          · exact ih tailTyped remaining

private theorem zip_positions {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (length : ids.length = codes.length) : (ids.zip codes).map Prod.fst = ids := by
  induction ids generalizing codes with
  | nil => simp
  | cons head tail ih =>
      cases codes with
      | nil => simp at length
      | cons code rest =>
          simp only [List.length_cons, Nat.succ.injEq] at length
          simp only [List.zip_cons_cons, List.map_cons, ih length]

/-- Original indirect lowering and raw Source typing construct the receipt
internally; no Header-indexed factory or emitted type equality is supplied. -/
theorem indirect_of_accepted {childFuel : Nat} {id : ExpressionId} {node : ExpressionNode}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (found : (source named).lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (pointwise : PointwiseFor root (source named) scope id rootReasonAt)
    (typed : ExpressionHasType (source named) sourceContext id node.type)
    (unique : NodeOccurrencesUnique (source named))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered) :
    Nonempty (IndirectReceipt root (sourceContext := sourceContext) (scope := scope)
      childFuel id callee ids metadata lowered) := by
  obtain ⟨actual, reported, read⟩ := accepted_read root found (by simp only [form, extraForm]) pointwise accepted
  have actualMetadata := CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ read)
  have nodeEq := Option.some.inj (actualMetadata.found.symm.trans found)
  subst actual
  obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions found form pointwise.special read form accepted
  have actualNode := Option.some.inj
    ((CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ compiler.read)).found.symm.trans compiler.found)
  have parentMetadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named)
      id compiler.original compiler.type := actualNode ▸ CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ compiler.read)
  have nodeMetadata := CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ compiler.read)
  have nodeId : compiler.node.id = id := (lookupExpression?_sound nodeMetadata.found).2
  obtain ⟨prepared⟩ := CallableIndexedOwnedIndirectSourceAdapters.Prepared.of_receipt compiler
    compiled.indexed.ancestry.graph.inputs.callable [] root.callables nodeId
  obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, application⟩ :=
    CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts unique found form typed
  have arity : ids.length = metadata.argumentCount := by
    cases application with
    | intro count _ _ _ => exact (row_length argumentsTyped).trans count.symm
  have sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler :=
    ⟨parentMetadata.requirements, parentMetadata.coercions, arity⟩
  obtain ⟨physicalCount, children⟩ := compiler.ordered_children
  have positions : compiler.entries.map Prod.fst = callee :: ids := by
    simp only [CallableIndirectCallCertificates.Receipt.entries, List.map_cons, zip_positions physicalCount]
  have generated : ∀ child code, (child, code) ∈ compiler.entries → ∃ childNode,
      (source named).lookupExpression? child = some childNode ∧
      ExpressionHasType (source named) sourceContext child childNode.type ∧
      SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed named) (source named) scope child rootReasonAt = .ok code := by
    intro child code member
    have childTyped : ∃ type, ExpressionHasType (source named) sourceContext child type := by
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact ⟨_, calleeTyped⟩
      · exact row_member argumentsTyped (List.of_mem_zip remaining).1
    obtain ⟨childType, typing⟩ := childTyped
    obtain ⟨childNode, contains, stored⟩ := typing.stored_type
    exact ⟨childNode, lookupExpression?_complete unique contains, (by rw [stored]; exact typing), children child code member⟩
  exact ⟨⟨compiler, prepared, sourceParent, parentMetadata, positions, physicalCount, generated⟩⟩

/-- The extra receipt is manufactured from this actual compiler branch.
Lambda bodies are deliberately not collected here; indirect children retain
one original receipt's callee-first physical vector and smaller child fuel. -/
theorem extra_receipts
    (domain : Domain root expressionSyntax callerEvidence headers (sourceContext := sourceContext)
      (scope := scope) (readFuel := readFuel))
    (unique : NodeOccurrencesUnique (source named))
    (childFuel : Nat) (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (allowed : expressionSyntax (source named) id) (found : (source named).lookupExpression? id = some node)
    (extra : extraForm node.form) (typed : ExpressionHasType (source named) sourceContext id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody (childFuel + 1)
      (context compiled.indexed named) (source named) scope id rootReasonAt = .ok lowered) :
    ∃ entries : List (ExpressionId × SourceCoreBasic.LoweredExpr),
      Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope)
        (CompatibleExpressionCalls.Entries scope entries) scope id lowered ∧
      entries.map Prod.fst = extraChildren node.form ∧
      ∀ child code, (child, code) ∈ entries → ∃ childNode,
        (source named).lookupExpression? child = some childNode ∧
        ExpressionHasType (source named) sourceContext child childNode.type ∧
        SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody childFuel
          (context compiled.indexed named) (source named) scope child rootReasonAt = .ok code := by
  have pointwise := pointwise_extra root expressionSyntax callerEvidence headers domain allowed found extra
  rcases extra_cases extra with ⟨parameters, result, statements, form⟩ | ⟨callee, ids, metadata, form⟩
  · obtain ⟨actual, reported, actualRead⟩ := accepted_read root found extra pointwise accepted
    have parentMetadata := CompatibleExpressionReads.metadata_of_read (pointwise.read ▸ actualRead)
    have same := Option.some.inj (parentMetadata.found.symm.trans found)
    subst actual
    have read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
        (source named) id = .ok (node, reported) := pointwise.read ▸ actualRead
    have special : DecoratedFunctionCode.SpecialPasses root.selected.policy root.selected.lowerBody childFuel
        (context compiled.indexed named) (source named) scope id rootReasonAt := pointwise.special _ _
    obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special parentMetadata.owner found
      (pointwise.read.trans read) form accepted
    have annotation := congrArg SourceCoreBasic.LoweredExpr.type certificate.emitted
    have metadata : CompatibleExpressionReads.Metadata compiled.compatible.checked (source named) id node lowered.type :=
      annotation.symm ▸ parentMetadata
    refine ⟨[], .lambda allowed found form certificate accepted typed metadata, ?_, ?_⟩
    · simp only [List.map_nil, form, extraChildren]
    · intro child code member; cases member
  · obtain ⟨receipt⟩ := indirect_of_accepted root found form pointwise typed unique accepted
    exact ⟨receipt.compiler.entries, .indirect found form receipt (fun _ _ member => ⟨rfl, member⟩),
      by simpa only [form, extraChildren] using receipt.positions, receipt.generated⟩

/-- Original compiler-fuel induction constructs the finite same-source Tree
and its expression sites once. Neither a final Tree nor an arbitrary extra
receipt is a premise. A selected Principal instantiates Named/Compilation and
callerEvidence with its actual cached compilation and dictionary. -/
theorem tree_of_accepted
    (domain : Domain root expressionSyntax callerEvidence headers (sourceContext := sourceContext)
      (scope := scope) (readFuel := readFuel))
    (unique : NodeOccurrencesUnique (source named))
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : AcceptedAt root expressionSyntax readFuel (source named) sourceContext scope id lowered) :
    RuntimeExpressionsFor (Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope))
      readFuel (.initial compiled.compatible.checked) (source named) sourceContext
      (context compiled.indexed named).solvedRequirements rootReasonAt scope id lowered := by
  cases receipt with
  | intro found typed allowed declarations closed residual signatures accepted =>
      exact tree_of_functions_at_runtime_with_children (headers := headers)
        (values := .initial compiled.compatible.checked) (compilation := context compiled.indexed named)
        callerEvidence (Head root expressionSyntax callerEvidence headers (sourceContext := sourceContext) (scope := scope))
        (include_named root expressionSyntax callerEvidence headers) (projected root expressionSyntax callerEvidence headers)
        extraForm extraChildren domain.admission domain.coverage domain.sourceTypes domain.emptyEvidence domain.order
        unique declarations signatures domain.constructorValid domain.fragmentValid domain.selectedValid
        (policy_for_all root expressionSyntax callerEvidence headers domain) compiled.indexed.ancestry.graph.inputs.callable
        [] root.callables domain.fragmentCoercions domain.coercions
        (extra_receipts root expressionSyntax callerEvidence headers domain unique) allowed found typed accepted

section Principal
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  (principalRoot : RootPolicyReceipt (compiled := compiled) principal.named
    principal.cached.diagnostics principal.cached.code principal.cached.compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- Specialization retains the actual selected method and its dictionary. The
generic finite producer uses its cached compilation directly. -/
theorem tree_of_principal
    (domain : Domain principalRoot expressionSyntax (some principal.dictionary) headers
      (sourceContext := sourceContext) (scope := scope) (readFuel := readFuel))
    (unique : NodeOccurrencesUnique (source principal.named))
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : AcceptedAt principalRoot expressionSyntax readFuel (source principal.named)
      sourceContext scope id lowered) :
    RuntimeExpressionsFor (Head principalRoot expressionSyntax (some principal.dictionary) headers
      (sourceContext := sourceContext) (scope := scope)) readFuel (.initial compiled.compatible.checked)
      (source principal.named) sourceContext (context compiled.indexed principal.named).solvedRequirements
      rootReasonAt scope id lowered :=
  tree_of_accepted principalRoot expressionSyntax (some principal.dictionary) headers domain unique receipt

end Principal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedRawCompilerHeads
