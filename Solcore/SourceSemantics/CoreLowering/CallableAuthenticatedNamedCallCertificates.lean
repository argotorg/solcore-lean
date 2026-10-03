import Solcore.SourceSemantics.CoreLowering.CallableCoercionRawNamedCallBuiltinArguments

/-! Authenticated direct calls retain the real special-hook receipt. Their
children use the existing open expression Tree, without pretending that the
ordinary selectedSignature branch accepted a caller with evidence. Only reached
ordinary callee headers are required. Runtime laws are not certificate fields. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedNamedCallCertificates
open Core Frontend SourceInference GeneralHeap
open CallableCoercionExpressionCertificates CallableCoercionRawNamedCallCertificates RecursiveNamedCatalog
abbrev Scope := SourceCoreLocalCell.Scope

variable {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}
  (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
    instantiation reasonAt policy node output)

/-- The argument family is an index, not a runtime assumption. All selection,
source, dictionary and ordered-code fields come from the actual direct call. -/
structure RawCall (context : SourceSemantics.Context) (children : GenericExpressionMeaning.Certificate)
    (header : Header prepared values ambient.definitions program) where
  reached : Reached receipt (headers := headers) header
  rawType : node.rawType = header.function.resultType
  calleeNode : ExpressionNode
  name : String
  calleeFound : source.lookupExpression? callee = some calleeNode
  calleeForm : calleeNode.form = .reference name (.declaration header.instantiation)
  calleeRequirements : calleeNode.requirements = []
  calleeCoercions : calleeNode.coercions = []
  valid : SourceSemantics.DeclarationInstantiation.Valid context header.instantiation
  evidence : header.function.evidence = []
  dictionary : ∀ evidence, Dynamic.DirectCallProducesEvidence context evidence node.requirements node.coercions instantiation.predicates []
  sequence : DataExpressionSequence.Tree source children scope arguments
    (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments
  nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd

theorem of_direct {context : SourceSemantics.Context} {children : GenericExpressionMeaning.Certificate}
    (reached : Reached receipt (headers := headers) header)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = program.signatures)
    (typed : ExpressionHasType source context id node.type)
    (sequence : DataExpressionSequence.Tree source children scope arguments
      (header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (nativeTypes : receipt.loweredArguments.map (·.type) = header.bindings.map Prod.snd) :
    Nonempty (RawCall receipt context children (headers := headers) header) := by
  obtain ⟨rawType, calleeNode, name, found, form, requirements, coercions, valid⟩ :=
    CallableCoercionRawNamedCallAdmission.source_types receipt reached sourceTypes unique signatures typed
  exact ⟨⟨reached, rawType, calleeNode, name, found, form, requirements, coercions, valid,
    sourceTypes.evidence header reached.member, source_dictionary receipt unique reached.predicates typed, sequence, nativeTypes⟩⟩

theorem RawCall.emitted {context : SourceSemantics.Context} {children : GenericExpressionMeaning.Certificate}
    (certified : RawCall receipt context children (headers := headers) header)
    (coercions : node.coercions = []) :
    output = ⟨header.output, SourceCoreCalls.call header.named.signature
      (scope.length + compilation.administrativePrefix + header.slot)
      (SourceCoreCalls.packArguments receipt.loweredArguments).expression compilation.internalReason⟩ := by
  have accepted := receipt.suffix.accepted
  rw [coercions] at accepted
  have same : receipt.operand = output := Except.ok.inj accepted
  exact same.symm.trans (by simpa only [certified.reached.signature, certified.reached.slot, header.resultType] using receipt.native.emitted)

/-- This head keeps the real .some receipt, including its actual callback and
fuel. Empty output coercions identify the whole result with the emitted call. -/
inductive Head (headers : Inventory prepared values ambient.definitions program)
    (compilerProgram : CheckedProgram) (compilation : SourceCoreFunctions.Context)
    (source : TypedSource) (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (children : GenericExpressionMeaning.Certificate) (scope : SourceCoreLocalCell.Scope) :
    ExpressionId → Lowered → Prop where
  | direct {project : Projector} {caller : Specialized} {child : SourceCoreEvidence.Child} {fuel : Nat}
      {id callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
      {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : Lowered}
      {header : Header prepared values ambient.definitions program}
      (receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
        instantiation reasonAt policy node output)
      (certified : RawCall receipt context children (headers := headers) header)
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node header.output)
      (sourceType : node.type = header.function.resultType) :
      Head headers compilerProgram compilation source context reasonAt children scope id output

abbrev Tree (headers : Inventory prepared values ambient.definitions program)
    (compilerProgram : CheckedProgram) (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (source : TypedSource) (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word) :=
  CompatibleExpressionCalls.Tree (Head headers compilerProgram compilation source context reasonAt)
    readFuel values source context compilation.solvedRequirements reasonAt

private theorem raw_type {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type) (coercions : node.coercions = []) :
    node.rawType = node.type := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | intro contains raw rawEq _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst same
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    exact rawEq

theorem head_of_direct {context : SourceSemantics.Context} {children : GenericExpressionMeaning.Certificate}
    (certified : RawCall receipt context children (headers := headers) header)
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context id node.type)
    (owner : id.occurrence.owner = source.owner)
    (projection : values.checked.catalog.project header.function.resultType = .ok header.output)
    (requirements : node.requirements = []) (coercions : node.coercions = []) :
    Head headers compilerProgram compilation source context reasonAt children scope id output := by
  have sourceType := (raw_type unique receipt.found typed coercions).symm.trans certified.rawType
  have metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node header.output :=
    ⟨receipt.found, owner, requirements, coercions, sourceType ▸ projection⟩
  exact .direct receipt certified metadata sourceType

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem tree_projected {readFuel : Nat} {source : TypedSource} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word} {scope : Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Tree headers compilerProgram compilation readFuel source context reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | fragment child => exact child.projected found
  | node head _ =>
    cases head with
    | primitive primitive =>
      cases primitive with
      | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _
        | binary metadata _ _ _ _ _ _ _ _ _ | conditional metadata _ _ _ _ _ _ _ _ _ _ =>
        have same := Option.some.inj (metadata.found.symm.trans found)
        exact same ▸ metadata.projected
    | constructor receipt _ _ _ =>
      have same := Option.some.inj (receipt.metadata.found.symm.trans found)
      exact same ▸ receipt.metadata.projected
    | member metadata _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected
    | index header _ _ _ _ _ =>
      have same := Option.some.inj (header.metadata.found.symm.trans found)
      exact same ▸ header.metadata.projected
    | builtin builtin =>
      cases builtin with
      | contracted metadata _ _ _ _ =>
        have same := Option.some.inj (metadata.found.symm.trans found)
        exact same ▸ metadata.projected
    | tuple receipt _ =>
      have same := Option.some.inj (receipt.metadata.found.symm.trans found)
      exact same ▸ receipt.metadata.projected
    | call call =>
      cases call with
      | direct receipt certified metadata _ =>
        have same := Option.some.inj (metadata.found.symm.trans found)
        have outputType := congrArg (fun code : Lowered => code.type) (certified.emitted receipt metadata.coercions)
        simpa only [same, outputType] using metadata.projected

private theorem compiled_children
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok code →
      Tree headers compilerProgram compilation readFuel source context reasonAt scope id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) ∧
      ∀ id code, (id, code) ∈ ids.zip codes →
        Tree headers compilerProgram compilation readFuel source context reasonAt scope id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, rfl, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, projected, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_, ?_⟩
      · simp [List.mapM_cons, ← sourceType, tree_projected child found, projected, bind, Except.bind]
      · intro other otherCode member
        rcases List.mem_cons.mp member with same | remaining
        · cases same; exact child
        · exact children other otherCode remaining


/-- Initial extraction grammar: complete builtin fragments and recursively
nested direct named calls. Named children of other operator heads are a later
factory extension, even though the generic semantic Tree can express them. -/
inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | builtin {id : ExpressionId} (fragment : CompatibleExpressionBuiltins.Syntax source id) : Syntax source id
  | direct {id callee : ExpressionId} {node : ExpressionNode} {arguments : List ExpressionId}
      {instantiation : DeclarationInstantiation}
      (found : source.lookupExpression? id = some node)
      (form : node.form = .call callee arguments (.declaration instantiation))
      (requirements : node.requirements = []) (coercions : node.coercions = [])
      (children : ∀ argument, argument ∈ arguments → Syntax source argument) : Syntax source id

/-- Static equality of the real hook. In particular its child callback is
passed through unchanged; no equality to lowerContextualExpression is assumed. -/
structure PolicyFor (policy : SourceCoreFunctions.Policy) (compilerProgram : CheckedProgram)
    (caller : Specialized) (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) : Prop where
  builtin : CompatibleExpressionBuiltins.PolicyFor policy compilation readFuel values source scope reasonAt
  direct : ∀ id node callee arguments instantiation,
    source.lookupExpression? id = some node → node.form = .call callee arguments (.declaration instantiation) →
    Syntax source id → ∀ child budget,
    (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option Lowered))
      | some special => special compilation child budget source scope id reasonAt) =
    SourceCoreEvidence.lowerWithProjector compilerProgram policy.projectType caller compilation child budget source scope id reasonAt policy.callables

/-- Only actually authenticated direct sites require an ordinary full header.
Both retained substitution orders stay in Reached, independently of this law. -/
def Coverage (headers : Inventory prepared values ambient.definitions program)
    (compilerProgram : CheckedProgram) (caller : Specialized) (compilation : SourceCoreFunctions.Context)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) : Prop :=
  ∀ project child fuel policy id callee arguments instantiation node output,
    Syntax source id → ∀ receipt : Direct compilerProgram project caller compilation child fuel source scope id callee arguments
      instantiation reasonAt policy node output,
    ∃ header, Nonempty (Reached receipt (headers := headers) header)

private theorem not_none
    {compilerProgram : CheckedProgram} {project : Projector} {caller : Specialized}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {arguments : List ExpressionId} {instantiation : DeclarationInstantiation} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
    (nonempty : caller.assumptions ≠ []) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation)) :
    SourceCoreEvidence.lowerWithProjector compilerProgram project caller compilation child fuel source scope id reasonAt policy ≠ .ok none := by
  intro accepted
  unfold SourceCoreEvidence.lowerWithProjector at accepted
  simp only [found, form, bind, Except.bind, pure, Except.pure] at accepted
  have nonemptyBool : caller.assumptions.isEmpty = false := by
    cases actual : caller.assumptions with
    | nil => exact False.elim (nonempty actual)
    | cons _ _ => rfl
  simp only [nonemptyBool, Bool.not_false, Bool.not_true, Bool.and_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte] at accepted
  repeat first | split at accepted | cases accepted


/-- Extract only the two initial grammar branches from the actual traversal.
The hook receives the real min-budget child, and its ordered results are used
without relowering or exchanging source metadata. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {caller : Specialized} {readFuel : Nat} {context : SourceSemantics.Context}
    (nonempty : caller.assumptions ≠ [])
    (policyFor : PolicyFor policy compilerProgram caller compilation readFuel values source scope reasonAt)
    (coverage : Coverage headers compilerProgram caller compilation source scope reasonAt)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = program.signatures)
    (nativeSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (coercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (projectPolicy : policy.projectType = SourceCoreCompatibleDataExpressions.projectType values.checked)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : Lowered}
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    Tree headers compilerProgram compilation readFuel source context reasonAt scope id lowered := by
  induction fuel generalizing id node lowered with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel ih =>
    cases syntaxTree with
    | builtin fragment =>
      exact .fragment (CompatibleExpressionBuiltins.tree_of_functions_with_validity unique declarations nativeSignatures
        constructorValid policyFor.builtin native active profile coercions fragment found typed accepted)
    | @direct _ callee originalNode arguments instantiation originalFound form requirements empty childSyntax =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst originalNode
      let callback : SourceCoreEvidence.Child := fun budget childSource childScope childId childReasonAt =>
        SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation childSource childScope childId childReasonAt
      have hook := policyFor.direct id node callee arguments instantiation found form
        (.direct found form requirements empty childSyntax) callback (fuel + 1)
      have owner : id.occurrence.owner = source.owner := by
        by_cases owned : id.occurrence.owner = source.owner
        · exact owned
        · simp [SourceCoreFunctions.lowerExpressionWithPolicy, owned, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
      obtain ⟨special, specialEq⟩ : ∃ special, policy.lowerSpecial? = some special := by
        cases actual : policy.lowerSpecial? with
        | none =>
          have impossible : SourceCoreEvidence.lowerWithProjector compilerProgram policy.projectType caller compilation callback (fuel + 1)
              source scope id reasonAt policy.callables = .ok none := by simpa only [actual] using hook.symm
          exact False.elim (not_none nonempty found form impossible)
        | some special => exact ⟨special, rfl⟩
      have hook := (show special compilation callback (fuel + 1) source scope id reasonAt = _ from by simpa only [specialEq] using hook)
      have selected : SourceCoreEvidence.lowerWithProjector compilerProgram policy.projectType caller compilation callback (fuel + 1)
          source scope id reasonAt policy.callables = .ok (some lowered) := by
        rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
        simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, specialEq, bind, Except.bind, pure, Except.pure] at accepted
        rw [hook] at accepted
        cases actualResult : SourceCoreEvidence.lowerWithProjector compilerProgram policy.projectType caller compilation callback (fuel + 1)
          source scope id reasonAt policy.callables with
        | error error => simp only [actualResult] at accepted; cases accepted
        | ok result =>
          cases result with
          | none => exact False.elim (not_none nonempty found form actualResult)
          | some output =>
            simp only [actualResult, Except.ok.injEq] at accepted
            cases accepted
            rfl
      obtain ⟨receipt⟩ := direct_of_accepted found form selected
      obtain ⟨header, ⟨reached⟩⟩ := coverage policy.projectType callback (fuel + 1) policy.callables id callee arguments instantiation node lowered
        (.direct found form requirements empty childSyntax) receipt
      have argumentsTyped := CallableCoercionRawNamedCallScalarArguments.argument_types receipt reached sourceTypes unique typed
      have argumentsAccepted : arguments.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt)
          = .ok receipt.loweredArguments := by
        simpa only [callback, Nat.min_eq_right (Nat.le_succ fuel)] using receipt.argumentsAccepted
      obtain ⟨count, nodes, projected, children⟩ := compiled_children unique argumentsTyped argumentsAccepted
        (fun child member node code found typed accepted => ih (childSyntax child member) found typed accepted)
      have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header reached.member))
      have sequence := CompatibleExpressionConstructors.sequence_of_nodes
        (certificate := CompatibleExpressionCalls.Entries scope (arguments.zip receipt.loweredArguments)) count nodes
        (fun child code member => ⟨rfl, member⟩)
      obtain ⟨certified⟩ := of_direct receipt reached sourceTypes unique signatures typed sequence nativeTypes
      have outputType := congrArg (fun code : Lowered => code.type) (certified.emitted receipt empty)
      have projected := CompatibleExpressionReads.projectType_of_accepted
        (by simpa only [projectPolicy] using receipt.suffix.outputProjection)
      have sourceType := (raw_type unique found typed empty).symm.trans certified.rawType
      have metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node header.output :=
        ⟨found, owner, requirements, empty, by simpa only [outputType] using projected⟩
      exact .node (.call (.direct receipt certified metadata sourceType)) children

private theorem builtin_ordinary_general {source : TypedSource} {locals : SourceCoreLocalPolymorphism.Catalog}
    {owner : SourceSpecialization.SpecializationKey} (ordinary : CompatibleExpressionBuiltins.Ordinary source locals owner) :
    CompatibleExpressionGeneral.Ordinary source locals owner :=
  ⟨fun id node child => ordinary.requirements id node (.fragment child),
   fun id node child => ordinary.coercions id node (.fragment child),
   fun id child => ordinary.notInitializer id (.fragment child),
   fun id node name binder child => ordinary.localBinder id node name binder (.fragment child)⟩

private theorem builtin_contextual_source
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals owner) (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | fragment child => exact CompatibleExpressionGeneral.contextualSource_fragment program plan locals owner parent (builtin_ordinary_general ordinary) child
  | proxy found form | unary found form _ | binary found form _ _ | group found form _ | pair found form _ _ | conditional found form _ _ _ | constructor found form _ | member found form _ | index found form _ _ _ | builtin found form _ =>
      simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem builtin_evidence_none (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = CompatibleExpressionLiterals.owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinaryOwned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
      if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
          ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
        some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
    simp
  cases syntaxTree with
  | fragment old => exact CompatibleExpressionGeneral.evidence_fragment program projector caller context child fuel scope reasonAt callables old found requirements coercions
  | proxy originalFound form | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ | constructor originalFound form _ | member originalFound form _ | index originalFound form _ _ _ | builtin originalFound form _ =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinaryOwned, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem builtin_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | fragment child => exact CompatibleExpressionGeneral.fragment_has_node child
  | proxy found _ | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ | constructor found _ _ | member found _ _ | index found _ _ _ _ | builtin found _ _ => exact ⟨_, found⟩


/-- The parent-free contextual compiler supplies the exact hook policy. The
caller is its real selected full record and may carry nonempty assumptions. -/
theorem tree_of_contextual
    {representation : SourceCoreGeneralFunctions.Representation} {signatures : ProgramSignatures}
    {locals : SourceCoreLocalPolymorphism.Catalog} {parents : List SourceCoreLocalEvidence.Prepared}
    {assignments : SourceCoreAssignmentFaultSites.Table} {diagnostics : SourceCoreDataPlaceFaultSites.Program}
    {native : SourceCoreGeneralFunctions.CallableContext} {skipInitializer : Option ExpressionId}
    {readFuel : Nat} {context : SourceSemantics.Context}
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (nonempty : caller.assumptions ≠ [])
    (coverage : Coverage headers compilerProgram caller compilation source scope reasonAt)
    (sourceTypes : RecursiveNamedExpressionCompilerCertificates.SourceTypes headers context)
    (unique : NodeOccurrencesUnique source) (sourceSignatures : context.signatures = program.signatures)
    (nativeSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals compilation.owner)
    (notInitializer : ∀ id node callee arguments instantiation, source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Syntax source id →
      locals.bindings.find? (fun binding => decide (binding.caller = compilation.owner ∧ binding.initializer = id)) = none)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (projectPolicy : representation.expressions.projectType = SourceCoreCompatibleDataExpressions.projectType values.checked)
    (syntaxTree : Syntax source id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compilerProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok output) :
    Tree headers compilerProgram compilation readFuel source context reasonAt scope id output := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    dsimp only at accepted
    simp only [callerSelected, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
    refine tree_of_functions nonempty ?policyProof coverage sourceTypes unique sourceSignatures nativeSignatures declarations
      constructorValid ordinary.coercions ?projectProof native [] ?profileProof syntaxTree found typed accepted
    case projectProof => exact projectPolicy
    case profileProof => rfl
    refine ⟨⟨?_, ?_, lowerPolicy, leafPolicy⟩, ?_⟩
    · intro childId childTree child budget
      obtain ⟨childNode, childFound⟩ := builtin_has_node childTree
      dsimp only
      rw [builtin_contextual_source compilerProgram compilation.plan locals compilation.owner none ordinary childTree]
      simp only [childFound, ordinary.notInitializer _ childTree, Option.filter]
      rw [builtin_evidence_none compilerProgram _ caller compilation child budget scope reasonAt _ childTree childFound
        (ordinary.requirements _ _ childTree childFound) (ordinary.coercions _ _ childTree childFound)]
      cases childForm : childNode.form <;> simp only
      case reference name resolution =>
        cases resolution <;> simp only
        case «local» binder =>
          rw [ordinary.localBinder _ _ _ _ childTree childFound childForm]
          rfl
    · intro childId childTree
      change (do
        let viewed ← SourceCoreGeneralFunctions.contextualSource compilerProgram compilation.plan locals compilation.owner none source childId
        representation.expressions.readExpression viewed childId) = _
      rw [builtin_contextual_source compilerProgram compilation.plan locals compilation.owner none ordinary childTree]
      simp only [bind, Except.bind, readPolicy]
    · intro childId childNode callee arguments instantiation childFound childForm childSyntax child budget
      dsimp only
      have viewed : SourceCoreGeneralFunctions.contextualSource compilerProgram compilation.plan locals compilation.owner none source childId = .ok source := by
        simp [SourceCoreGeneralFunctions.contextualSource, childFound, childForm, bind, Except.bind, pure, Except.pure]
      rw [viewed]
      simp only [childFound, notInitializer _ _ _ _ _ childFound childForm childSyntax, Option.filter]
      cases actualResult : SourceCoreEvidence.lowerWithProjector compilerProgram _ caller compilation child budget source scope childId reasonAt _ with
      | error error => rfl
      | ok result => cases result <;> simp only [childForm]

end Solcore.SourceSemantics.CoreLowering.CallableAuthenticatedNamedCallCertificates
