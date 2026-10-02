import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameterNativeTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionScalarNativeTyping

/-! Native typing is assembled before a lambda Code exists. Actual compiler
receipts retain the parameter fold, manifest, frame snapshot and descriptor.
The body profile is restricted to one scalar return or tail expression. Source
typing, ordinary admission and lexical frame placement remain static inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping
open Core Frontend SourceInference
open CallableIndexedParameterNativeTyping CallableIndexedLambdaCertificates

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapped_fields {α ε : Type} {items : List α} {fields : List (Word × Ty)}
    {action : α → Except ε (Word × Ty)} {definitions : DataEnvironment}
    (valid : ∀ item ∈ items, ∀ field, action item = .ok field → field.2.WellFormed definitions)
    (accepted : items.mapM action = .ok fields) :
    ∀ field ∈ fields, field.2.WellFormed definitions := by
  induction items generalizing fields with
  | nil => simp at accepted; subst fields; simp
  | cons item rest ih =>
    simp only [List.mapM_cons, bind, Except.bind] at accepted
    cases head : action item with
    | error error => simp [head] at accepted
    | ok field =>
      simp only [head] at accepted
      obtain ⟨tail, generated, same⟩ := bind_ok accepted
      cases same
      intro selected member
      rcases List.mem_cons.mp member with rfl | member
      · exact valid item (by simp) _ head
      · exact ih (fun item h => valid item (List.mem_cons_of_mem _ h)) generated selected member

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {convert : ε → δ} {value : α}
    (accepted : action.mapError convert = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- All metadata annotations in the actual manifest are the supplied lexical
scope annotations. The successful hook's source/binder selection is retained. -/
theorem manifest_native {checked : SourceCoreCompatibleCatalog.Checked}
    {inventory : SourceCoreLambdaTemplates.Inventory checked}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {node : ExpressionNode} {parameter result : Ty} {body emitted : Expr}
    (accepted : SourceCoreLambdaTemplates.hook inventory owner active compilation source scope node parameter result body = .ok emitted)
    {definitions : DataEnvironment} {context : Core.Context}
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed definitions)
    (references : ∀ (position : Nat) (binding : Resolved.LocalId × Ty), scope[position]? = some binding →
      context[position]? = some (OptionalCell.referenceType binding.2))
    (bodyTyped : HasType (parameter :: context) body (LanguageResult.resultType result) definitions) :
    HasType (parameter :: context) emitted (LanguageResult.resultType result) definitions := by
  simp only [SourceCoreLambdaTemplates.hook, bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw] at accepted
  repeat' first | split at accepted | contradiction
  rename_i _ template selected metadata header _ fields fieldsAccepted _ checkedScope scopeChecks
  cases accepted
  apply SourceCoreLambdaTemplates.manifestBody_hasType _ ?_
    (SourceCoreSourceCells.captures_hasType scope id references) bodyTyped
  have generated := mapError_ok fieldsAccepted
  change ((do
      unless (scope.map Prod.fst).Nodup do throw SourceCoreLambdaTemplates.Error.duplicateScope
      scope.mapM fun (binder, type) => do
        let row ← match template.context.bindingAt? binder with
          | some row => pure row
          | none => throw (SourceCoreLambdaTemplates.Error.scopeMismatch binder)
        pure (row.key, type)) : Except SourceCoreLambdaTemplates.Error (List (Word × Ty))) = .ok fields at generated
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at generated
  split at generated
  · apply mapped_fields (items := scope) ?_ generated
    intro binding member field emitted
    split at emitted
    · cases emitted; exact scopeWF binding member
    · cases emitted
  · cases generated

theorem certificate_native {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      prepared.ancestry.layout.frame prepared.base.globals.length
      (prepared.layouts.allocatorAt compilation.owner [] (fun error => .sourceAllocation (reprStr error)))))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates compilation.owner [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner id []))
    (administrativePrefix : compilation.administrativePrefix = 1)
    (bundle : receipt.parameterCore = packed (receipt.loweredParameters.map Prod.snd))
    (parameterWF : ∀ binding ∈ receipt.loweredParameters, binding.2.WellFormed checked.catalog.definitions)
    (ordinary : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (administrative : Core.Context)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type))
    (bodyTyped : HasType (SourceCoreLocalCell.coreContext receipt.bodyScope ++ administrative)
      receipt.body (LanguageResult.resultType receipt.resultCore) prepared.layouts.definitions) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions := by
  have extension := (CallableIndexedAmbient.ambientDefinitions prepared).basePrefix
  have parameterTyped := (CompatibleExpressionReads.projectType_wellFormed (projector ▸ receipt.parameterProjected)).extend_definitions extension
  have resultTyped := (CompatibleExpressionReads.projectType_wellFormed (projector ▸ receipt.resultProjected)).extend_definitions extension
  have accepted := receipt.allocated
  simp only [parameterBody, allocation] at accepted
  have bodyScope := (FunctionCode.Parameters.of_accepted receipt.parametersCompiled).scope
  rw [bodyScope, ← List.map_reverse] at bodyTyped
  have allocated := CallableIndexedParameterNativeTyping.of_accepted _ accepted
    (CallableIndexedAmbient.frame_registered prepared) resultTyped
    (fun binding member => (parameterWF binding member).extend_definitions extension)
    ordinary administrative current bodyTyped
  rw [← bundle] at allocated
  have raw := manifest_native (manifest ▸ receipt.bodyHook)
    (fun binding member => (scopeWF binding member).extend_definitions extension) (context := SourceCoreLocalCell.coreContext scope ++ administrative)
    (by
      intro position binding found
      rw [List.getElem?_append_left (by simpa [SourceCoreLocalCell.coreContext] using (List.getElem?_eq_some_iff.mp found).1)]
      simp [SourceCoreLocalCell.coreContext, found, OptionalCell.referenceType]) allocated
  obtain ⟨origin, actualBody, _, rawEq, _, globals, _, emitted⟩ :=
    CallableIndexedFormation.expressionHook_receipt prepared.ancestry (expressionHook ▸ receipt.expressionHook)
  have sameBody := (Expr.lambda.inj rawEq).2.2
  rw [← sameBody] at emitted
  have lambdaTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) receipt.rawLambda
      (.function receipt.parameterCore (LanguageResult.resultType receipt.resultCore)) prepared.layouts.definitions := by
    rw [emitted]
    exact SourceCoreCallableIndexedAncestry.snapshotLambda_hasType
      (CallableIndexedAmbient.frame_registered prepared) _ _ parameterTyped resultTyped
      (by simpa [SourceCoreCallableIndexedAncestry.creationReferenceIndex, administrativePrefix, globals] using current) raw
  have decorated := receipt.decoration
  rw [callables, ActualCallablePolicy.lambda_decoration _ [] compilation view node id receipt.parameterCore receipt.resultCore _ descriptor] at decorated
  have sameExpression := Except.ok.inj decorated
  have checkedType := receipt.checked
  rw [callables] at checkedType
  unfold SourceCoreBasic.ensureType at checkedType
  split at checkedType
  · rename_i sameType
    change reported = CallableContract.functionType receipt.parameterCore receipt.resultCore at sameType
    have typed := LanguageResult.success_hasType (descriptor.wrap_hasType (TaggedFunction.anonymous_hasType lambdaTyped))
    simpa only [receipt.emitted, ← sameExpression, sameType] using typed
  · cases checkedType

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at checked
  split at checked
  · assumption
  · cases checked

/-- Invert the actual single-return/tail compiler action. The output records
the real child callback and result-type check, including the finish wrapper. -/
theorem scalar_body_receipt {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode} {type : Ty}
    {expression : ExpressionId} {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (read : policy.readStatement source statement = .ok (node, type))
    (form : node.form = .returnStmt (some expression) ∨ node.form = .expression expression false)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope [statement] result reasonAt fellThrough escaped = .ok code) :
    ∃ budget lowered,
      policy.lowerExpression budget source scope expression reasonAt = .ok lowered ∧
      lowered.type = result ∧
      code = LocalControl.finish result (LocalLoop.toControl result
        (LocalLoop.returnValue result lowered.expression) escaped)
        (if result = .unit then LanguageResult.success .unit else LanguageResult.failure result (.word fellThrough)) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, same⟩ := bind_ok accepted
  cases same
  cases fuel with
  | zero => cases generated
  | succ fuel =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy, read, bind, Except.bind, pure, Except.pure] at generated
    rcases form with form | form
    all_goals
      simp only [form, Bool.not_false, Bool.true_and, List.isEmpty_nil, ↓reduceIte] at generated
    · obtain ⟨checkedUnit, _, generated⟩ := bind_ok generated
      cases checkedUnit
      obtain ⟨lowered, child, generated⟩ := bind_ok generated
      obtain ⟨checkedUnit, checked, generated⟩ := bind_ok generated
      cases checkedUnit
      cases generated
      exact ⟨fuel, lowered, child, (ensure_same checked).symm, rfl⟩
    · obtain ⟨lowered, child, generated⟩ := bind_ok generated
      obtain ⟨checkedUnit, _, generated⟩ := bind_ok generated
      cases checkedUnit
      obtain ⟨checkedUnit, checked, generated⟩ := bind_ok generated
      cases checkedUnit
      cases generated
      exact ⟨fuel, lowered, child, (ensure_same checked).symm, rfl⟩

theorem scalar_body_native {policy : SourceCoreLoops.Policy}
    {expressions : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {expressionBudget : Nat} {compilation : SourceCoreFunctions.Context}
    {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId} {node : StatementNode} {type : Ty}
    {expression : ExpressionId} {expressionNode : ExpressionNode} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    {sourceContext : SourceSemantics.Context} {definitions : DataEnvironment}
    (callback : policy.lowerExpression = FunctionCode.children expressions lowerBody expressionBudget compilation)
    (read : policy.readStatement source statement = .ok (node, type))
    (form : node.form = .returnStmt (some expression) ∨ node.form = .expression expression false)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope [statement] result reasonAt fellThrough escaped = .ok code)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (ordinary : CompatibleExpressionConditionals.PolicyFor expressions compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, CompatibleExpressionConditionals.Syntax source id →
      source.lookupExpression? id = some node → node.coercions = [])
    (syntaxTree : CompatibleExpressionConditionals.Syntax source expression)
    (found : source.lookupExpression? expression = some expressionNode)
    (sourceTyped : ExpressionHasType source sourceContext expression expressionNode.type)
    (scopeWF : CompatibleExpressionScalarNativeTyping.ScopeWellFormed values.checked.catalog.definitions scope)
    (extension : values.checked.catalog.definitions.Extends definitions)
    (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code (LanguageResult.resultType result) definitions := by
  obtain ⟨budget, lowered, generated, same, emitted⟩ := scalar_body_receipt read form accepted
  rw [callback] at generated
  have tree := CompatibleExpressionConditionals.tree_of_functions unique declarations ordinary coercions syntaxTree found sourceTyped generated
  obtain ⟨wellFormed, typed⟩ := CompatibleExpressionScalarNativeTyping.conditionals_native_at scopeWF administrative extension tree
  rw [same] at wellFormed typed
  rw [emitted]
  apply LocalControl.finish_hasType wellFormed (LocalLoop.toControl_hasType escaped wellFormed (LocalLoop.returnValue_hasType wellFormed typed))
  split
  · rename_i unitResult
    simpa only [unitResult] using
      (LanguageResult.success_hasType (HasType.unit (definitions := definitions)
        (context := SourceCoreLocalCell.coreContext scope ++ administrative)))
  · exact LanguageResult.failure_hasType wellFormed .word

private theorem scope_wellFormed {definitions : DataEnvironment} {scope : SourceCoreLocalCell.Scope}
    (all : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed definitions) :
    CompatibleExpressionScalarNativeTyping.ScopeWellFormed definitions scope := by
  induction scope with
  | nil => exact .empty _
  | cons head tail ih => exact (ih (fun binding member => all binding (List.mem_cons_of_mem _ member))).prepend head.1 (all head (by simp))

private theorem projected_parameters {checked : SourceCoreCompatibleCatalog.Checked}
    (bindings : List CallableIndexedParameterCertificates.Binding)
    (projected : ∀ binding ∈ bindings, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2) :
    checked.catalog.project (TypeSystem.Ty.productMany (bindings.map (fun binding => binding.1.scheme.body))) =
      .ok (packed (bindings.map Prod.snd)) := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    have head := CompatibleExpressionReads.projectType_of_accepted (projected binding (by simp))
    cases rest with
    | nil => exact head
    | cons next tail =>
      have rest := ih (fun item member => projected item (List.mem_cons_of_mem _ member))
      change (do pure (Ty.product (← checked.catalog.project binding.1.scheme.body)
        (← checked.catalog.project (TypeSystem.Ty.productMany ((next :: tail).map
          (fun binding : CallableIndexedParameterCertificates.Binding => binding.1.scheme.body)))))) = _
      rw [head, rest]
      rfl

private theorem binder_projection {checked : SourceCoreCompatibleCatalog.Checked}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {binder : TypedBinder} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.lowerBinder checked source scope binder = .ok type) :
    SourceCoreCompatibleDataExpressions.projectType checked (.binder binder.id) binder.scheme.body = .ok type := by
  simp only [SourceCoreCompatibleDataExpressions.lowerBinder, bind, Except.bind,
    throw, throwThe, MonadExceptOf.throw] at accepted
  repeat' first | split at accepted | contradiction
  exact accepted

/-- The actual contextual binder action supplies every checked projection.
Monomorphic admission is source metadata, not a fact recovered from native types. -/
theorem parameter_projections {checked : SourceCoreCompatibleCatalog.Checked}
    {representation : SourceCoreGeneralFunctions.Representation} {locals : SourceCoreLocalPolymorphism.Catalog}
    {owner : SourceSpecialization.SpecializationKey} {policy : SourceCoreFunctions.Policy}
    {source : TypedSource} {scope finalScope : SourceCoreLocalCell.Scope}
    {parameters : List TypedBinder} {bindings : List CallableIndexedParameterCertificates.Binding}
    (accepted : SourceCoreFunctions.lambdaParameters policy source scope parameters = .ok (bindings, finalScope))
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder representation locals owner [])
    (ordinaryPolicy : representation.expressions.lowerBinder = SourceCoreCompatibleDataExpressions.lowerBinder checked)
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = []) :
    ∀ binding ∈ bindings, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2 := by
  have tree := FunctionCode.Parameters.of_accepted accepted
  clear accepted
  induction tree with
  | nil => simp
  | @cons scope finalScope parameter parameters type bindings head tail ih =>
    rw [binderPolicy, SourceCoreGeneralFunctions.contextualBinder,
      monomorphic parameter (by simp), List.isEmpty_nil, if_pos rfl, ordinaryPolicy] at head
    intro binding member
    rcases List.mem_cons.mp member with rfl | member
    · exact binder_projection head
    · exact ih (fun binder h => monomorphic binder (List.mem_cons_of_mem _ h)) binding member

/-- Static scalar source profile at the real body callback. Every expression
certificate is subsequently extracted from that callback's successful output;
no body or child native typing or execution field is stored here. -/
structure ScalarBody {checked : SourceCoreCompatibleCatalog.Checked}
    (values : SourceCoreCompatibleValues.Context) (sameChecked : values.checked = checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered) where
  loopPolicy : SourceCoreLoops.Policy
  callback : lowerBody (FunctionCode.children policy lowerBody fuel compilation) = SourceCoreLoops.lowerStatementsWithPolicy loopPolicy
  expressionCallback : loopPolicy.lowerExpression = FunctionCode.children policy lowerBody fuel compilation
  statement : StatementId
  statementNode : StatementNode
  statementType : Ty
  singleton : statements = [statement]
  expression : ExpressionId
  expressionNode : ExpressionNode
  read : loopPolicy.readStatement view statement = .ok (statementNode, statementType)
  form : statementNode.form = .returnStmt (some expression) ∨ statementNode.form = .expression expression false
  sourceContext : SourceSemantics.Context
  readFuel : Nat
  unique : NodeOccurrencesUnique view
  declarations : CompatibleExpressionReads.ScopeDeclarations view receipt.bodyScope sourceContext
  ordinary : CompatibleExpressionConditionals.PolicyFor policy compilation readFuel values view receipt.bodyScope reasonAt
  coercions : ∀ id node, CompatibleExpressionConditionals.Syntax view id → view.lookupExpression? id = some node → node.coercions = []
  syntaxTree : CompatibleExpressionConditionals.Syntax view expression
  found : view.lookupExpression? expression = some expressionNode
  sourceTyped : ExpressionHasType view sourceContext expression expressionNode.type

theorem scalar_certificate_native {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {reported : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Certificate policy lowerBody fuel compilation view scope id node parameters result statements reported reasonAt lowered)
    (values : SourceCoreCompatibleValues.Context) (sameChecked : values.checked = checked)
    (body : ScalarBody values sameChecked receipt)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      prepared.ancestry.layout.frame prepared.base.globals.length
      (prepared.layouts.allocatorAt compilation.owner [] (fun error => .sourceAllocation (reprStr error)))))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates compilation.owner [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry compilation.owner [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.lambda compilation.owner id []))
    (administrativePrefix : compilation.administrativePrefix = 1)
    (parameterProjections : ∀ binding ∈ receipt.loweredParameters, SourceCoreCompatibleDataExpressions.projectType checked
      (.binder binding.1.id) binding.1.scheme.body = .ok binding.2)
    (ordinary : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (administrative : Core.Context)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) prepared.layouts.definitions := by
  have binderTree := FunctionCode.Parameters.of_accepted receipt.parametersCompiled
  have projected := projected_parameters receipt.loweredParameters parameterProjections
  have parameter := CompatibleExpressionReads.projectType_of_accepted (projector ▸ receipt.parameterProjected)
  have bundle : receipt.parameterCore = packed (receipt.loweredParameters.map Prod.snd) := by
    have sameTypes : receipt.loweredParameters.map (fun binding => binding.1.scheme.body) =
        parameters.map (·.scheme.body) := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map (fun binder : TypedBinder => binder.scheme.body)) binderTree.binders
    rw [sameTypes, receipt.parameterTypes] at projected
    exact Except.ok.inj (parameter.symm.trans projected)
  have parameterWF := fun binding member => CompatibleExpressionReads.projectType_wellFormed (parameterProjections binding member)
  have allBody : ∀ binding : Resolved.LocalId × Ty, binding ∈ receipt.bodyScope → binding.2.WellFormed checked.catalog.definitions := by
    rw [binderTree.scope]
    intro binding member
    rcases List.mem_append.mp member with fromParameters | fromScope
    · rcases List.mem_map.mp (List.mem_reverse.mp fromParameters) with ⟨parameter, parameterMember, sameBinding⟩
      rw [← sameBinding]
      exact parameterWF parameter parameterMember
    · exact scopeWF binding fromScope
  have accepted := receipt.bodyCompiled
  rw [body.callback] at accepted
  have accepted : SourceCoreLoops.lowerStatementsWithPolicy body.loopPolicy fuel view receipt.bodyScope
      [body.statement] receipt.resultCore reasonAt compilation.internalReason compilation.internalReason = .ok receipt.body :=
    by simpa only [body.singleton] using accepted
  have native := scalar_body_native body.expressionCallback body.read body.form accepted body.unique body.declarations
    body.ordinary body.coercions body.syntaxTree body.found body.sourceTyped
    (by simpa only [sameChecked] using scope_wellFormed allBody)
    (by simpa only [sameChecked] using (CallableIndexedAmbient.ambientDefinitions prepared).basePrefix) administrative
  exact certificate_native prepared receipt projector allocation manifest expressionHook callables descriptor
    administrativePrefix bundle parameterWF ordinary scopeWF administrative current native



private theorem descriptor_exists (table : SourceCoreStageCodebook.Table)
    {origin : SourceCoreStageCodebook.Origin} {id : Word} (selected : table.idAt? origin = some id) :
    Nonempty (SourceCoreCallableContracts.Descriptor table origin) := by
  cases accepted : SourceCoreCallableContracts.descriptor table origin with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at accepted
    split at accepted
    · rename_i absent
      rw [selected] at absent
      cases absent
    · cases accepted
  | ok descriptor => exact ⟨descriptor⟩


open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration

/-- The accepted contextual site is formed with native typing derived from its
actual scalar callback and parameter fold. The receipt below predates Code; it
contains compiler equations, not a native typing or body execution field.
Static callback profiles, source typing and frame placement remain explicit. -/
theorem of_contextual {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compiled : Compilation prepared named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (captured : Dynamic.Environment)
    (profile : checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : prepared.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context prepared named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []) prepared.base.sourceProgram.signatures
      prepared.base.locals compiled.parents compiled.own.assignments diagnostics (context prepared named)
      prepared.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    (receipt : Certificate policy lowerBody fuel (context prepared named) view scope id node
      parameters result body reported reasonAt lowered)
    (values : SourceCoreCompatibleValues.Context) (sameChecked : values.checked = checked)
    (scalar : ScalarBody values sameChecked receipt)
    (projector : policy.projectType = SourceCoreCompatibleDataExpressions.projectType checked)
    (allocation : policy.sourceCells = some (allocator prepared named))
    (manifest : policy.rawLambdaBody = SourceCoreLambdaTemplates.hook prepared.ancestry.templates named.signature.key [])
    (expressionHook : policy.rawLambdaExpression = SourceCoreCallableIndexedAncestry.expressionHook prepared.ancestry named.signature.key [])
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
    (binderPolicy : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
      (representation prepared) prepared.base.locals named.signature.key [])
    (monomorphic : ∀ binder ∈ parameters, binder.scheme.quantified = [])
    (ordinaryParameters : ∀ binder ∈ parameters, view.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (scopeWF : ∀ binding : Resolved.LocalId × Ty, binding ∈ scope → binding.2.WellFormed checked.catalog.definitions)
    (current : (SourceCoreLocalCell.coreContext scope ++ administrative)[scope.length + 1 + prepared.base.globals.length]? =
      some (.cell prepared.ancestry.layout.frame.type)) :
    ∃ site : Site prepared named parameters result body sourceContext evidence captured scope administrative,
      site.code.id = id ∧ site.code.lowered = lowered := by
  have hook := receipt.expressionHook
  rw [expressionHook] at hook
  obtain ⟨origin, _, selected, _, _, _, _, _⟩ :=
    CallableIndexedFormation.expressionHook_receipt prepared.ancestry hook
  rw [(lookupExpression?_sound found).2] at selected
  obtain ⟨descriptor⟩ := descriptor_exists _ selected
  have projections := parameter_projections receipt.parametersCompiled binderPolicy (by rfl) monomorphic
  have ordinaryBindings : ∀ binding ∈ receipt.loweredParameters,
      view.inputs.any (fun input => decide (input.id = binding.1.id)) = false := by
    intro binding member
    apply ordinaryParameters binding.1
    rw [← (FunctionCode.Parameters.of_accepted receipt.parametersCompiled).binders]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  have native := scalar_certificate_native prepared receipt values sameChecked scalar projector allocation manifest
    expressionHook callables descriptor rfl projections ordinaryBindings scopeWF administrative current
  exact CallableIndexedLambdaGeneration.of_contextual prepared compiled record sourceContext evidence captured profile
    viewOfSource sourceFound sourceForm found form owner requirements coercions ordinary read accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaScalarNativeTyping
