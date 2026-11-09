import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeLambdas
import Solcore.SourceSemantics.Internal.Inference.ExecutableInterfaces
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.Internal.Checking.TypingCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.CallerMethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndexDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionConstructors
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionReads
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.StageMeaning
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.IndirectExpressionHeads

/-!
# Selected compilations: expression bounds

Graded bounds of selected expressions: reads, literals, pairs, tuples, constructors and operators, with their read admission and sequencing.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompilerCoercedExpressionProfile
/-! Flat original call metadata and leaf argument forms. The profile contains
no recursive expression grammar; the accepted action supplies its children. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CompilerCoercedExpressionProfile
open Core Frontend SourceInference
open AcceptedNamedExpressionFlow (LeafForm)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedPrimitiveSourceAdmission (nativeMetadata?)

def LeafAt (source : TypedSource) (id : ExpressionId) : Prop :=
  ∃ node, source.lookupExpression? id = some node ∧ LeafForm node.form

def leaf? (source : TypedSource) (id : ExpressionId) : Option (PLift (LeafAt source id)) := do
  match found : source.lookupExpression? id with
  | none => none
  | some node =>
    match form : node.form with
    | .reference name (.local binder) =>
      pure ⟨node, found, form ▸ LeafForm.read name binder⟩
    | .reference name (.builtinBoolean value) =>
      pure ⟨node, found, form ▸ LeafForm.literal (.bool name value)⟩
    | .literal value => pure ⟨node, found, form ▸ LeafForm.literal (.word value)⟩
    | .integerLiteral value resolution =>
      pure ⟨node, found, form ▸ LeafForm.literal (.integer value resolution)⟩
    | .tuple [] => pure ⟨node, found, form ▸ LeafForm.literal .unit⟩
    | _ => none

private def allLeaves? (source : TypedSource) :
    (ids : List ExpressionId) → Option (PLift (∀ id ∈ ids, LeafAt source id))
  | [] => some ⟨by intro id member; cases member⟩
  | id :: ids => do
    let ⟨head⟩ ← leaf? source id
    let ⟨tail⟩ ← allLeaves? source ids
    pure ⟨by
      intro child member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail child member⟩

structure Profile (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SourceSpecialization.SpecializedFunction) (expression : ExpressionId) where
  node : ExpressionNode
  callee : ExpressionId
  arguments : List ExpressionId
  instantiation : DeclarationInstantiation
  found : source.lookupExpression? expression = some node
  form : node.form = .call callee arguments (.declaration instantiation)
  coercions : node.coercions ≠ []
  requirements : node.requirements ≠ []
  children : ∀ argument ∈ arguments, LeafAt source argument
  initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  direct : DirectSite rows instantiation
  metadataAccepted : ∃ receipt, nativeMetadata? compiled.indexed named source = some receipt

def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (rows : List SourceSpecialization.SpecializedFunction) (expression : ExpressionId) :
    Option (Profile compiled named source rows expression) := do
  match metadataAccepted : nativeMetadata? compiled.indexed named source with
  | none => none
  | some receipt =>
    match found : source.lookupExpression? expression with
    | none => none
    | some node =>
      match form : node.form with
      | .call callee arguments (.declaration instantiation) =>
        if coercions : node.coercions ≠ [] then
          if requirements : node.requirements ≠ [] then do
            let ⟨children⟩ ← allLeaves? source arguments
            if initializer : compiled.indexed.base.locals.bindings.find? (fun binding =>
                decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
                  binding.initializer = expression)) = none then do
              let ⟨direct⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.directSite? rows instantiation
              pure ⟨node, callee, arguments, instantiation, found, form, coercions, requirements,
                children, initializer, direct, receipt, metadataAccepted⟩
            else none
          else none
        else none
      | _ => none

theorem Profile.metadata {compiled : SourceCoreUnifiedCompilation.Compiled}
    {named : SourceCoreGeneralFunctions.Function} {source : TypedSource}
    {rows : List SourceSpecialization.SpecializedFunction} {expression : ExpressionId}
    (profile : Profile compiled named source rows expression) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed named source (fun _ => False) := by
  obtain ⟨⟨metadata⟩, _⟩ := profile.metadataAccepted
  exact metadata

end Solcore.SourceSemantics.CoreLowering.CompilerCoercedExpressionProfile
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorInterfaces
/-! Actual operator preparation verifies convention names at selected source
sites. The original node and primary requirement identity survive complete
rigid specialization, including expressions inside lambda bodies. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorInterfaces
open Frontend SourceInference TypeSystem
open ExecutableCoercionInterfaces
open CallableCoercionPreparationSteps (bind_ok OperatorForm operatorOwnedNode)

private theorem require_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then action else .error error) = .ok value) :
    condition ∧ action = .ok value := by
  split at accepted
  · exact ⟨‹condition›, accepted⟩
  · cases accepted

theorem ordinary_of_layout {node : ExpressionNode} {requirements : List RequirementId}
    (layout : node.requirements = requirements ++ node.coercions.flatMap CoercionStep.requirements) :
    SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements := by
  unfold SourceCompilationPlan.ordinaryOwnedRequirements?
  change (if node.requirements.length < (node.coercions.flatMap CoercionStep.requirements).length
    then none else
    let owned := node.requirements.take
      (node.requirements.length - (node.coercions.flatMap CoercionStep.requirements).length)
    if node.requirements = owned ++ node.coercions.flatMap CoercionStep.requirements
    then some owned else none) = some requirements
  rw [layout]
  simp

theorem unary_interface
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {operator : Syntax.UnaryOp} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
    {primary : RequirementId} {companions : List RequirementId} {name methodName : String}
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (primary :: companions))
    (dispatch : Detail.unaryOperatorDispatch operator = .traitMethod name methodName)
    (accepted : SourceCompilationPlan.checkedUnaryOperatorMethod program caller node available operator = .ok selection) :
    ∃ solved trait,
      caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) = [solved] ∧
      solved.predicate.trait = .declaration trait ∧
      (program.signatures.trait? trait).map (·.name) = some name := by
  simp only [SourceCompilationPlan.checkedUnaryOperatorMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i profile profileFound
  rcases profile with ⟨traitName, actualMethod⟩
  have profileDispatch : Detail.unaryOperatorDispatch operator = .traitMethod traitName actualMethod := by
    cases operator <;> cases profileFound <;> rfl
  have sameName : traitName = name := by
    have same := profileDispatch.symm.trans dispatch
    cases same
    rfl
  rw [owned] at accepted
  dsimp only at accepted
  split at accepted <;> try contradiction
  obtain ⟨solved, picked, accepted⟩ := bind_ok accepted
  have selected : caller.function.solvedRequirements.filter
      (fun row => decide (row.id = primary)) = [solved] := by
    change (match caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) with
      | [] => .error (.missingSolvedRequirement caller.key node.id primary)
      | [row] => .ok row
      | rows => .error (.duplicateSolvedRequirements caller.key node.id primary rows.length) :
      Except SourceTypedRuntime.RuntimeError SolvedRequirement) = .ok solved at picked
    cases filtered : caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) with
    | nil => simp [filtered] at picked
    | cons row rest =>
      cases rest with
      | nil => simp only [filtered, Except.ok.injEq] at picked; subst solved; rfl
      | cons other rest => simp [filtered] at picked
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  split at accepted <;> try contradiction
  rename_i traitId goalTrait
  split at accepted <;> try contradiction
  rename_i trait found
  obtain ⟨guard, _⟩ := require_ok accepted
  exact ⟨solved, traitId, selected, goalTrait, by
    simp only [found, Option.map_some]
    exact congrArg some (guard.trans sameName)⟩

theorem binary_interface
    {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {operator : Syntax.BinaryOp} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
    {primary : RequirementId} {companions : List RequirementId} {name methodName : String}
    (owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (primary :: companions))
    (dispatch : Detail.binaryOperatorDispatch operator = .traitMethod name methodName)
    (accepted : SourceCompilationPlan.checkedBinaryOperatorMethod program caller node available operator = .ok selection) :
    ∃ solved trait,
      caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) = [solved] ∧
      solved.predicate.trait = .declaration trait ∧
      (program.signatures.trait? trait).map (·.name) = some name := by
  simp only [SourceCompilationPlan.checkedBinaryOperatorMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i profile profileFound
  rcases profile with ⟨traitName, actualMethod⟩
  have profileDispatch : Detail.binaryOperatorDispatch operator = .traitMethod traitName actualMethod := by
    cases operator <;> cases profileFound <;> rfl
  have sameName : traitName = name := by
    have same := profileDispatch.symm.trans dispatch
    cases same
    rfl
  rw [owned] at accepted
  dsimp only at accepted
  split at accepted <;> try contradiction
  obtain ⟨solved, picked, accepted⟩ := bind_ok accepted
  have selected : caller.function.solvedRequirements.filter
      (fun row => decide (row.id = primary)) = [solved] := by
    change (match caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) with
      | [] => .error (.missingSolvedRequirement caller.key node.id primary)
      | [row] => .ok row
      | rows => .error (.duplicateSolvedRequirements caller.key node.id primary rows.length) :
      Except SourceTypedRuntime.RuntimeError SolvedRequirement) = .ok solved at picked
    cases filtered : caller.function.solvedRequirements.filter (fun row => decide (row.id = primary)) with
    | nil => simp [filtered] at picked
    | cons row rest =>
      cases rest with
      | nil => simp only [filtered, Except.ok.injEq] at picked; subst solved; rfl
      | cons other rest => simp [filtered] at picked
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  split at accepted <;> try contradiction
  rename_i traitId goalTrait
  split at accepted <;> try contradiction
  rename_i trait found
  obtain ⟨guard, _⟩ := require_ok accepted
  exact ⟨solved, traitId, selected, goalTrait, by
    simp only [found, Option.map_some]
    exact congrArg some (guard.trans sameName)⟩

theorem of_covered {program : CheckedProgram}
    {caller : SourceSpecialization.SpecializedFunction} {plan : SourceSpecializationWorklist.Plan}
    (covered : CallableCoercionPreparation.CoveredWith program caller plan) :
    OperatorInterfaces program.signatures caller.function.solvedRequirements caller.function.typedBody := by
  obtain ⟨available, _, covered⟩ := covered
  intro node member primary companions name layout dispatch
  have ordinary := ordinary_of_layout layout
  have form : OperatorForm node := by
    cases nodeForm : node.form <;> simp only [operatorDispatch, nodeForm] at dispatch
    all_goals first | contradiction | simp only [OperatorForm, nodeForm]
  obtain ⟨visit⟩ := (covered node member).2 (primary :: companions) ordinary (by simp) form
  have sameRequirements : visit.requirements = primary :: companions :=
    Option.some.inj (visit.owned.symm.trans ordinary)
  have owned : SourceCompilationPlan.ordinaryOwnedRequirements?
      (operatorOwnedNode node visit.requirements) = some (primary :: companions) := by
    apply ordinary_of_layout
    simp only [operatorOwnedNode, List.flatMap_nil, List.append_nil, sameRequirements]
  have accepted := visit.selected
  cases nodeForm : node.form <;>
    simp only [operatorDispatch, nodeForm] at dispatch
  all_goals try contradiction
  case unary operator operand =>
    obtain ⟨method, dispatch⟩ := dispatch
    change (match node.form with
      | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller
          (operatorOwnedNode node visit.requirements) available operator
      | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller
          (operatorOwnedNode node visit.requirements) available operator
      | _ => .error (.unsupportedRequirements visit.requirements)) = .ok visit.selection at accepted
    rw [nodeForm] at accepted
    exact unary_interface (program := program) (caller := caller)
      (node := operatorOwnedNode node visit.requirements) (available := available)
      (operator := operator) (selection := visit.selection) owned dispatch accepted
  case binary left operator right =>
    obtain ⟨method, dispatch⟩ := dispatch
    change (match node.form with
      | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller
          (operatorOwnedNode node visit.requirements) available operator
      | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller
          (operatorOwnedNode node visit.requirements) available operator
      | _ => .error (.unsupportedRequirements visit.requirements)) = .ok visit.selection at accepted
    rw [nodeForm] at accepted
    exact binary_interface (program := program) (caller := caller)
      (node := operatorOwnedNode node visit.requirements) (available := available)
      (operator := operator) (selection := visit.selection) owned dispatch accepted

private theorem filter_applied (substitution : ParameterSubstitution)
    (requirements : List SolvedRequirement) (id : RequirementId) :
    (requirements.map (SourceSpecialization.applySolvedRequirement substitution)).filter
        (fun row => decide (row.id = id)) =
      (requirements.filter (fun row => decide (row.id = id))).map
        (SourceSpecialization.applySolvedRequirement substitution) := by
  induction requirements with
  | nil => rfl
  | cons first rest ih =>
    by_cases same : first.id = id <;>
      simp [same, SourceSpecialization.applySolvedRequirement, ih]

private theorem map_singleton {α β : Type} {f : α → β} {items : List α} {value : β}
    (same : items.map f = [value]) : ∃ item, items = [item] ∧ f item = value := by
  cases items with
  | nil => cases same
  | cons item rest =>
    cases rest with
    | nil => exact ⟨item, rfl, (List.cons.inj same).1⟩
    | cons next tail => cases same

private theorem dispatch_applied (substitution : ParameterSubstitution)
    (node : ExpressionNode) (name : String) :
    operatorDispatch (SourceSpecialization.applyExpressionNode substitution node) name =
      operatorDispatch node name := by
  cases form : node.form <;>
    simp [operatorDispatch, SourceSpecialization.applyExpressionNode,
      SourceSpecialization.applyExpressionForm, form]

private theorem coercion_ids_applied (substitution : ParameterSubstitution)
    (steps : List CoercionStep) :
    (steps.map (SourceSpecialization.applyCoercionStep substitution)).flatMap CoercionStep.requirements =
      steps.flatMap CoercionStep.requirements := by
  induction steps with
  | nil => rfl
  | cons step rest ih => simp [ih]

/-- Rigid specialization leaves operator syntax and every requirement identity
unchanged. No inverse type substitution is needed to recover the original site. -/
theorem of_applied {signatures : ProgramSignatures} {function : CheckedFunction}
    {substitution : ParameterSubstitution}
    (supported : OperatorInterfaces signatures
      (SourceSpecialization.applyCheckedFunction substitution function).solvedRequirements
      (SourceSpecialization.applyCheckedFunction substitution function).typedBody) :
    OperatorInterfaces signatures function.solvedRequirements function.typedBody := by
  intro node member primary companions name layout dispatch
  have nodeMember : .expression (SourceSpecialization.applyExpressionNode substitution node) ∈
      (SourceSpecialization.applyCheckedFunction substitution function).typedBody.nodes :=
    List.mem_map.mpr ⟨.expression node, member, rfl⟩
  have appliedLayout : (SourceSpecialization.applyExpressionNode substitution node).requirements =
      (primary :: companions) ++
        (SourceSpecialization.applyExpressionNode substitution node).coercions.flatMap CoercionStep.requirements := by
    simpa only [SourceSpecialization.applyExpressionNode, coercion_ids_applied] using layout
  obtain ⟨actual, trait, selected, traitEq, nameEq⟩ := supported _ nodeMember
    primary companions name appliedLayout (by simpa only [dispatch_applied] using dispatch)
  change (function.solvedRequirements.map (SourceSpecialization.applySolvedRequirement substitution)).filter
    (fun row => decide (row.id = primary)) = [actual] at selected
  rw [filter_applied] at selected
  obtain ⟨original, singleton, applied⟩ := map_singleton selected
  refine ⟨original, trait, singleton, ?_, nameEq⟩
  rw [← applied] at traitEq
  exact traitEq

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorInterfaces
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationRootStaticSupport
/-! Static support for the pool-zero numeric family. The certificate belongs
  to the actual original Source and parameter context. The chosen terminal
  point retains its genuine receipt and selected scope. These structures store
  no execution, child meaning, Below law or desired body/application result.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRootStaticSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionState

/-- The eventual body carrier uses the concrete owned pool at universe zero. -/
def poolZero {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled program))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ProtectedStateTransition.Protocol.{0, 0} (Records keys) :=
  protocol headers keys

/-- Exact static authority at one original expression occurrence. Runtime
  validity and evidence coverage are propositions, not completed executions. -/
structure RootData (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) where
  compilerFuel : Nat
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody compilerFuel
    compilation invocation.source scope expression reasonAt = .ok lowered
  certificate : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Certificate
    policy lowerBody compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source context reasonAt scope expression lowered
  node : ExpressionNode
  found : invocation.source.lookupExpression? expression = some node
  rawResult : node.type = rawType
  typed : ExpressionHasType invocation.source context expression node.type
  sameLedger : context.solvedRequirements = compilation.solvedRequirements
  runtimeLedger : RuntimeRequirementLedgerValid context
  unique : NodeOccurrencesUnique invocation.source
  catalog : SignatureCatalogWellFormed (Program.ofChecked compiled.sourceProgram).signatures
  runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
    context invocation.source
  covers : invocation.evidence.Covers context
  actualFunctionType : policy.callables.functionType = CallableContract.functionType
  uninitialized : ∀ current id code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current id code →
    CallableLambdaBodyReachability.Reaches invocation.source [.expression expression] (.expression id) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)
  callsReady : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
    (compiled := compiled) (invocation := invocation) certificate

/-- A pool-only law covers precisely the legacy finite certificates. Its
absence of direct calls is derived from actual supported syntax. -/
structure Root (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep) extends
    RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults where
  noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods toRootData.certificate
  noDirect : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoDirect toRootData.certificate
  noIndexes : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoIndexes toRootData.certificate

/-- Direct-enabled roots retain selected static authority in the same ordered
finite Header inventory. Actual canonical slot values remain runtime inputs. -/
structure CanonicalRoot (compiled : SourceCoreUnifiedCompilation.Compiled)
    (policy : SourceCoreFunctions.Policy) (lowerBody : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (reasonAt : ExpressionId → Word) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    (rawType : TypeSystem.Ty) (semanticFaults : FunctionCalls.FaultRep)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))) extends
    RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults where
  noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods toRootData.certificate
  directReady : ∀ {fuel callScope callId callee ids instantiation callCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
      policy lowerBody fuel compilation (.initial compiled.compatible.checked)
      invocation.source callScope callId callee ids instantiation reasonAt callCode),
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler toRootData.certificate →
    Nonempty { port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence compiler headers context invocation.evidence //
        SelectedCompilationNamedSourceTyping.Certified port.header ∧
        SelectedCompilationSourceSignatureFacts.Shape port.header }
  indexReady : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady toRootData.certificate

/-- Existential packaging for the numeric IH. All compiler indices belong to
  the stored authentic Root; the ambient Source/context/scope/child stay fixed. -/
structure RootAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (semanticFaults : FunctionCalls.FaultRep) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  readFuel : Nat
  reasonAt : ExpressionId → Word
  rawType : TypeSystem.Ty
  support : Root compiled policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults

/-- Packaging does not change any Source, compiler or validity index. -/
def RootAt.ofRoot {compiled : SourceCoreUnifiedCompilation.Compiled}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}
    (root : Root compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults) :
    RootAt compiled context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

section RootConstruction
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}

/-- Legacy syntax proves the pool-only restriction for this exact extracted
certificate, including all recursively evaluated callee and argument entries. -/
def RootData.legacy
    (root : RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults)
    (syntaxTree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax invocation.source expression)
    (noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods root.certificate) :
    Root compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults :=
  ⟨root, noMethods, CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax root.certificate syntaxTree,
    CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax root.certificate syntaxTree⟩

/-- Shared roots receive full evidence authority derived at their actual
caller context, for each reached compiler occurrence. -/
def RootData.canonical_with
    (root : RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults)
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (ready : ∀ {fuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        policy lowerBody fuel compilation (.initial compiled.compatible.checked)
        invocation.source callScope callId callee ids instantiation reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler root.certificate →
      Nonempty { port : CallableIndexedOwnedPreparedStagedDirectCallAuthority.PortWithEvidence
        compiler headers context invocation.evidence // SelectedCompilationNamedSourceTyping.Certified port.header ∧
        SelectedCompilationSourceSignatureFacts.Shape port.header })
    (indexes : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady root.certificate)
    (noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods root.certificate) :
    CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults headers :=
  ⟨root, noMethods, ready, indexes⟩

/-- All reached direct sites use the original finite inventory and authentic
compiler context; no semantic call law or runtime globals are manufactured. -/
def RootData.canonical
    (root : RootData compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (certified : ∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
      SelectedCompilationNamedSourceTyping.Certified header ∧ SelectedCompilationSourceSignatureFacts.Shape header)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    (plan : compilation.plan = compiled.indexed.base.plan)
    (globals : compilation.globals = compiled.indexed.base.globals)
    (ordinarySites : ∀ {fuel callScope callId callee ids instantiation callCode}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
        policy lowerBody fuel compilation (.initial compiled.compatible.checked)
        invocation.source callScope callId callee ids instantiation reasonAt callCode),
      CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.DirectCalls compiler root.certificate →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Ordinary compilation.plan instantiation ∧
        compiler.node.requirements = [])
    (indexes : CallableIndexedOwnedPreparedStagedIndexDiagnosticAuthority.IndexReady root.certificate)
    (noMethods : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.NoMethods root.certificate) :
    CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) :=
  ⟨root, noMethods, fun compiler path => by
    obtain ⟨port⟩ := CallableIndexedOwnedPreparedStagedDirectCallAuthority.of_inventory compiler rows complete plan globals
    obtain ⟨ordinary, requirements⟩ := ordinarySites compiler path
    exact ⟨⟨⟨port, CallableIndexedOwnedPreparedStagedDirectCallAuthority.ordinary_evidence
      compiler port ordinary requirements context invocation.evidence⟩, certified port.header port.member⟩⟩, indexes⟩
end RootConstruction

/-- The direct-enabled numeric family keeps the same authentic static indices
and a finite inventory; the actual caller supplies its physical slot values. -/
structure CanonicalRootAt (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (context : SourceSemantics.Context) (invocation : Staging.Recursive.Scope)
    (scope : SourceCoreLocalCell.Scope) (expression : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) (semanticFaults : FunctionCalls.FaultRep) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  compilation : SourceCoreFunctions.Context
  readFuel : Nat
  reasonAt : ExpressionId → Word
  rawType : TypeSystem.Ty
  support : CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
    reasonAt scope expression lowered rawType semanticFaults headers

def CanonicalRootAt.ofRoot {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {expression : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {rawType : TypeSystem.Ty} {semanticFaults : FunctionCalls.FaultRep}
    (root : CanonicalRoot compiled policy lowerBody compilation readFuel context invocation
      reasonAt scope expression lowered rawType semanticFaults headers) :
    CanonicalRootAt compiled headers context invocation scope expression lowered semanticFaults :=
  ⟨policy, lowerBody, compilation, readFuel, reasonAt, rawType, root⟩

/-- The context is the actual retained EntryPrefix.Context. P receives static
  roots for every real Source-selected scope; R uses packet.child/selected.
  Guards and call authority are supplied at each such scope, rather than
  recovered from its Source equality alone. -/
structure SelectedBody {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    (code : Code compiled.indexed function localScope administrative)
    (inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
    (stages : Staging.Recursive.Registry)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages)
    (semanticFaults : FunctionCalls.FaultRep) where
  point : packet.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
    packet.expression packet.receipt.child
  readFuel : Nat
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure function child →
    Root compiled code.policy code.lowerBody code.compilation readFuel inputs.context child
      code.reasonAt
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child function.resultType semanticFaults

/-- Restriction uses the existing accepted-action singleton constructor.
  The original packet's policy, childFuel, reasonAt and selected scope remain. -/
abbrev selectedPoint {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {stages : Staging.Recursive.Registry}
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages) :=
  CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.narrow packet

/-- Every actual selected closure scope packages its original parameter Root.
  Preservation uses this projection for each Source-selected scope; reflection
  can use packet.child together with packet.selected. -/
def SelectedBody.rootAt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {localScope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context}
    {code : Code compiled.indexed function localScope administrative}
    {inputs : CallableIndexedLambdaEntryPrefix.Context
      (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code}
    {stages : Staging.Recursive.Registry}
    {packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages}
    {semanticFaults : FunctionCalls.FaultRep}
    (support : SelectedBody code inputs stages packet semanticFaults)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    RootAt compiled inputs.context child
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ localScope)
      packet.expression packet.receipt.child semanticFaults :=
  RootAt.ofRoot (support.roots child selected)

/-- Named support retains the real Header context and literal physical binding
  scope. Its expression compiler indices remain bundled, rather than guessed
  from the Header's statement policy. Original raw result and reasonAt remain
  tied to this actual Header; all genuine selected Source scopes are covered. -/
structure NamedSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (stages : Staging.Recursive.Registry)
    (packet : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header)
    (semanticFaults : FunctionCalls.FaultRep) where
  point : packet.certificate = CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds.Point
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    packet.expression packet.receipt.child
  roots : ∀ (child : Staging.Recursive.Scope), stages.Closure header.function child →
    { root : RootAt compiled header.context child
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        packet.expression packet.receipt.child semanticFaults //
      root.rawType = header.function.resultType ∧ root.reasonAt = header.reasonAt }

/-- Each contextual Association chooses its own actual BodyWith context.
  Neither the ordinary nor the principal branch invents context equality or
  converts that Support's arbitrary expression certificate family. -/
def ClosureSupportFor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association
      headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore)
    (stages : Staging.Recursive.Registry)
    (packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.TerminalFor association stages) : Type :=
  match association, packet with
  | .ordinary _ _ code _ support _ _ _ _ _ _, packet =>
      SelectedBody code support.body.toContext stages packet semanticFaults
  | .principal _ _ code _ support _ _ _ _ _ _, packet =>
      SelectedBody code support.body.toContext stages packet semanticFaults

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRootStaticSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationExpressionSequence
/-! Ordered staged arguments are constructed from the actual compiler Tree
and strictly smaller expression results. Each successful child passes its
actual reached caller state to the next child. Both failure tags retain the
same originating scope, token and final state. Native reflection reconstructs
an independent Source grade from the original packed-helper computation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationExpressionSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues DataExpressionSequence
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- Ordered child receipts retain the source types of every successful value. -/
structure PostAdmission (types : List TypeSystem.Ty) (outcome : Staging.Recursive.ValuesOutcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  rows : StableRows (bridge.pool reached)
  successful : ∀ values, outcome = .values values →
    Dynamic.ValuesHaveTypes context index.heap values types ∧ Admission bridge context reached

theorem PostAdmission.at_values {types : List TypeSystem.Ty} {values : List Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge types (context := context) (.values values) reached) :
    Admission bridge context reached := (post.successful values rfl).2

theorem PostAdmission.values_typed {types : List TypeSystem.Ty} {values : List Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge types (context := context) (.values values) reached) :
    Dynamic.ValuesHaveTypes context index.heap values types := (post.successful values rfl).1

theorem PostAdmission.at_fault_types {types other : List TypeSystem.Ty} {failure : Staging.Recursive.Failure}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge types (context := context) (.fault failure) reached) :
    PostAdmission bridge other (context := context) (.fault failure) reached :=
  ⟨post.rows, by intro _ impossible; cases impossible⟩

theorem PostAdmission.fault {types : List TypeSystem.Ty} {type : TypeSystem.Ty}
    {failure : Staging.Recursive.Failure}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge types (context := context) (.fault failure) reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨post.rows, by intro _ impossible; cases impossible⟩
  | stage origin call reason => exact post.rows

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem member_typing {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids types) :
    MemberTyping (context := context) (invocation := invocation) ids := by
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typing member found

variable {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
  {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}

private theorem preserves_values_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.values sources) after) (within : size ≤ budget) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) (.values sources) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
      cases execution
      exact ⟨[], store, mapping, world, .inRight .unit, .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial,
        admitted.rows, by intro values same; cases same; exact ⟨.nil, admitted⟩⟩
  | single found generated =>
      cases execution with
      | cons head tail =>
          cases tail
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | value payload =>
              exact ⟨[_], finalStore, finalMap, finalWorld, evaluated, .cons payload .nil,
                finalHeaps, maps, worlds, frame, metadata, reached, related, post.rows,
                by intro values same; cases same; exact ⟨.cons post.at_value.1 .nil, post.at_value.2⟩⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | cons head rest =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨values, finalStore, finalMap, finalWorld, second, restRep, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 rest
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              have nonempty : values ≠ [] := by
                intro absent
                have lengths := restRep.length.2
                simp [absent] at lengths
              refine ⟨coreValue :: values, finalStore, finalMap, finalWorld, ?_,
                .cons (model.extend payload maps worlds) restRep, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post.rows, by intro values same; cases same; exact ⟨.cons (firstPost.at_value.1.mono metadata) post.values_typed, post.at_values⟩⟩
              rw [rename_prefix] at second
              have combined := LocalSequence.pair_success lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second
              simpa [SourceCoreCalls.packArguments, pair_rename, packValues, nonempty] using combined

private theorem preserves_fault_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {failure : Staging.Recursive.Failure}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : Staging.Recursive.Size.Expressions program registry size invocation context environment
      before ids (.fault failure) after) (within : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) (.fault failure) reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ after with
  | nil => cases execution
  | single found generated =>
      cases execution with
      | headFault failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
      | tailFault _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      cases execution with
      | headFault failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, first, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted failed
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                maps, worlds, frame, metadata, reached, related, post.rows, by intro _ impossible; cases impossible⟩
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_left_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first
      | tailFault head failed =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (by simp)) within)
              generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
              initial admitted head
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨token, finalStore, finalMap, finalWorld, second, matched, finalHeaps,
                  maps, worlds, frame, metadata, reached, related, post⟩ :=
                ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix layout coreValue)
                  (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 failed
                  (Nat.le_trans (Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))) within)
              refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps,
                firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                reached, callerProtocol.trans firstRelated related, post.at_fault_types⟩
              rw [rename_prefix] at second
              simpa [SourceCoreCalls.packArguments, pair_rename] using LocalSequence.pair_right_failure lowered.type
                (SourceCoreCalls.packArguments (nextCode :: codes)).type first second

/-- Actual list typing supplies each used child's stored type. The successful
prefix retains the same cumulative caller records at every reached state. -/
theorem preserves_values (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ sources},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.values sources) after →
    size ≤ budget →
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) (.inRight .word (packValues values)) finalStore ∧
      Values model finalMap finalWorld sourceTypes (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) (.values sources) reached :=
  preserves_values_with_members bridge budget tree (member_typing unique typing)

/-- A failing argument stops the original helper at the same reached caller
pool; no later argument runs and neither failure tag is relabeled. -/
theorem preserves_fault (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before after store ξ failure},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    Staging.Recursive.Size.Expressions program registry size invocation context environment before ids (.fault failure) after →
    size ≤ budget →
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults failure token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) (.fault failure) reached :=
  preserves_fault_with_members bridge budget tree (member_typing unique typing)

private theorem reflects_with_members (budget : Nat)
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (evaluated : EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
      value finalStore) (within : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) outcome reached := by
  induction tree generalizing size mapping world actual actualContext before store ξ value finalStore with
  | nil =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (show Evaluates actual store
        ((SourceCoreCalls.packArguments []).expression.rename ξ) (.inRight .word .unit) store from .inRight .unit)
      exact ⟨_, .values [], before, mapping, world, .nil, .values (values := []) .nil, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial,
        admitted.rows, by intro values same; cases same; exact ⟨.nil, admitted⟩⟩
  | single found generated =>
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        children _ within generated found (sourceTyped _ (by simp) _ found)
          environments heaps locals layout actualTyped initial admitted evaluated
      cases represented with
      | value payload =>
          exact ⟨_, .values [_], after, finalMap, finalWorld, .cons trace .nil,
            .values (values := [_]) (.cons payload .nil), finalHeaps, maps, worlds, frame, metadata,
            reached, related, post.rows, by intro values same; cases same; exact ⟨.cons post.at_value.1 .nil, post.at_value.2⟩⟩
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace,
            .fault matched, finalHeaps, maps, worlds, frame, metadata,
            reached, related, post.rows, by intro _ impossible; cases impossible⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
      change EvaluationSize size actual store ((LocalSequence.pair lowered.type
        (SourceCoreCalls.packArguments (nextCode :: codes)).type lowered.expression
        (SourceCoreCalls.packArguments (nextCode :: codes)).expression).rename ξ) value finalStore at evaluated
      rw [pair_rename] at evaluated
      have complete := evaluated
      cases evaluated with
      | caseLeft first _ =>
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure lowered.type
                  (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .headFault trace, .fault matched,
                finalHeaps, maps, worlds, frame, metadata, reached, related, post.rows,
                by intro _ impossible; cases impossible⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            children _ (by omega) generated found (sourceTyped _ (by simp) _ found)
              environments heaps locals layout actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              rename_i middleStore coreValue
              have nextLayout : EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) ξ) canonical
                  (coreValue :: actual) := agree_prefix layout coreValue
              cases continuation with
              | caseLeft second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted (by omega)
                  cases result with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld, .tailFault firstTrace tailTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                        firstFrame.trans frame, firstMetadata.trans metadata,
                        reached, callerProtocol.trans firstRelated related, post.at_fault_types⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, tailTrace, result, finalHeaps,
                      maps, worlds, frame, metadata, reached, related, post⟩ :=
                    ih (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata) nextLayout
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted (by omega)
                  cases result with
                  | @values sources values restRep =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_success lowered.type
                          (SourceCoreCalls.packArguments (nextCode :: codes)).type first.sound second.sound)
                      have nonempty : values ≠ [] := by
                        intro absent
                        have lengths := restRep.length.2
                        simp [absent] at lengths
                      refine ⟨_, .values (sourceValue :: sources), after, finalMap, finalWorld,
                        .cons firstTrace tailTrace, ?_, finalHeaps,
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata,
                        reached, callerProtocol.trans firstRelated related, post.rows, by intro values same; cases same; exact ⟨.cons (firstPost.at_value.1.mono metadata) post.values_typed, post.at_values⟩⟩
                      simpa [packValues, nonempty] using
                        RecursiveStageArguments.ResultFor.values (codes := lowered :: nextCode :: codes)
                          (.cons (model.extend payload maps worlds) restRep)

/-- Original packed-helper inversion supplies strict native child bounds.
Each reflected Source child contributes its own independent list grade. -/
theorem reflects (budget : Nat) (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    {originalTypes : List TypeSystem.Ty} (unique : NodeOccurrencesUnique invocation.source)
    (typing : ExpressionsHaveTypes invocation.source context ids originalTypes) :
    ∀ (_children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    {mapping world administrativeContext actualContext environment canonical actual before store finalStore ξ value},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial → ∀ {size},
    EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore →
    size < budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expressions program registry sourceSize invocation context environment before ids outcome after ∧
      RecursiveStageArguments.ResultFor model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge sourceTypes (context := context) outcome reached :=
  reflects_with_members bridge budget tree (member_typing unique typing)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationExpressionSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadAdmission
/-! Ordinary reads preserve their actual Source cell and lazy mapping writes.
Only the selected occurrence and its input heap are used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleExpressionReads

theorem read_preserved
    {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel values source scope id reason code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {value : Dynamic.Value} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    (read : Dynamic.Heap.Reads before location cell)
    (ordinary : cell.generalized = none)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heap : Dynamic.HeapWellTyped context before)
    (typing : ExpressionHasType source context id type)
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    Dynamic.ExpressionEvaluationPreserved context before after value type := by
  have same_node : ∀ {node}, ContainsExpression source id node → node = certificate.node := by
    intro node contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
  have same_cell : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment certificate.binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    cases otherLookup.functional lookup
    exact otherRead.functional read
  cases typing with
  | @intro _ _ node rawType plan contains formTyped rawEq rawWF typeWF requirements =>
    cases same_node contains
    have path := requirements.outputPath
    rw [certificate.metadata.coercions] at path
    cases path
    cases trace with
    | intro otherContains raw coercions =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at coercions
      cases coercions
      rw [certificate.form] at raw formTyped
      obtain ⟨typed, afterTyped, extension⟩ := raw.referencePreserves locals heap formTyped
      exact ⟨typed, afterTyped, extension⟩
    | generalizedLocal otherContains form _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at form
      cases form
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadBounds
/-! Actual ordinary read receipts retain Source admission at the reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CompatibleExpressionReads
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {name : String} {binder : Resolved.LocalId} {failedScope call reason}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (coercions : node.coercions = [])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have reference : ∀ {shape requirements}, Staging.Recursive.Occurrence invocation id shape requirements →
      shape = .reference name (.local binder) := by
    intro shape requirements occurrence
    obtain ⟨other, contains, sameForm, _, _⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    exact sameForm.symm.trans form
  cases trace with
  | generalizedLocal contains _ _ _ _ _ _ _ path =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [coercions] at path
      cases path
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found coercions contains))
  | group occurrence _
  | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ | tupleFault occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases reference occurrence

/-- Reconstruct only an ordinary readable local, using its actual cell. The
generalized-local alternatives are excluded by that same cell's descriptor. -/
private theorem staged_of_read
    {fuel : Nat} {values : ValuesContext} {invocation : Staging.Recursive.Scope}
    {scope : Scope} {id : ExpressionId} {reason : Word} {code : Expr}
    (certificate : Certificate fuel values invocation.source scope id reason code)
    {program : Program} {registry : Staging.Recursive.Registry} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (lookup : Dynamic.Environment.LooksUp environment certificate.binder location)
    (read : Dynamic.Heap.Reads before location cell)
    (ordinary : cell.generalized = none)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
      environment before id outcome after) :
    Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
      invocation context environment before id
      (match outcome with | .value value => .value value | .fault fault => .fault (.semantic fault)) after := by
  have same_node : ∀ {other}, ContainsExpression invocation.source id other → other = certificate.node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans certificate.metadata.found)
  have same_cell : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment certificate.binder otherLocation →
      Dynamic.Heap.Reads before otherLocation otherCell → otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    have sameLocation := otherLookup.functional lookup
    subst otherLocation
    exact otherRead.functional read
  have contains := lookupExpression?_sound certificate.metadata.found
  have atomic : Staging.Recursive.AtomicForm certificate.node.form := by
    rw [certificate.form]
    exact .reference _ _
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro otherContains raw coercions =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at coercions
      cases coercions
      exact .atomicValue contains atomic certificate.metadata.coercions
        (by simpa only [certificate.metadata.coercions] using raw)
    | generalizedLocal otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form otherContains raw =>
      cases same_node otherContains
      exact .atomicFault contains atomic certificate.metadata.coercions
        (by simpa only [certificate.metadata.coercions] using raw)
    | coercion otherContains _ failed =>
      cases same_node otherContains
      rw [certificate.metadata.coercions] at failed
      cases failed
    | generalizedLocalRequirement otherContains otherForm _ otherLookup otherRead descriptor _ _ _
    | generalizedLocalCoercion otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      cases same_node otherContains
      rw [certificate.form] at otherForm
      cases otherForm
      cases same_cell otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {fuel : Nat} {reasonAt : ExpressionId → Word}
  {semanticFaults : FunctionCalls.FaultRep} {faults : RecursiveStageMeaning.FaultRep}
  (uninitialized : ∀ scope id lowered,
    LoweredRead fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "reads" => LoweredRead fuel (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) invocation.source context reasonAt

include extension semantic unique in
/-- The accepted local-read compiler discharges preservation internally. A
stage failure at this atomic occurrence is impossible; semantic failures keep
their original token, heap and actual caller state. -/
theorem preserves_local [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    PreservesAt bridge context model registry invocation
      (fun scope id lowered => reads scope id lowered ∧
        ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) faults size := by
  intro scope id lowered ⟨receipt, readFault⟩ node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  obtain ⟨_, selected, _, _, _, selectedRead, _, cellRep⟩ :=
    GenericHeap.lookup_visible environments heaps lookup certificate.slot
  have sameCell := read.functional selectedRead
  subst selected
  have plain : ∃ plainOutcome : Dynamic.ExpressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before id plainOutcome after ∧
      outcome = (match plainOutcome with | .value value => .value value | .fault reason => .fault (.semantic reason)) := by
    cases outcome with
    | value value => exact ⟨.value value, .value trace.sound.value_plain, rfl⟩
    | fault failure => cases failure with
      | semantic reason => exact ⟨.fault reason, .fault trace.sound.semanticFault_plain, rfl⟩
      | stage failedScope call reason =>
        exact False.elim (no_stage unique found (nodeEq ▸ certificate.form) (nodeEq ▸ certificate.metadata.coercions) trace)
  obtain ⟨plainOutcome, plainTrace, outcomeEq⟩ := plain
  obtain ⟨value, finalStore, evaluated, represented, finalHeaps, frame, metadata⟩ :=
    certificate.preserves functions extension program context invocation.evidence binding
      environments heaps locals agrees readFault unique plainTrace
  simp only [SourceCoreCompatibleValues.Context.initial, nodeEq, typeEq] at represented finalHeaps
  let transport := administrativeTransport headers keys
  let reachedPool := transport.extend (bridge.pool initial) (.refl _) (.refl _) frame metadata
  obtain ⟨reached, _poolEq, related⟩ := bridge.restore initial reachedPool (.refl _) (.refl _)
    frame metadata (transport.related (bridge.pool initial) (.refl _) (.refl _) frame metadata)
  refine ⟨value, finalStore, mapping, world, ?_, ?_, finalHeaps, .refl _, .refl _,
    frame, metadata, reached, related, ?_⟩
  · simpa only [← typeEq] using evaluated
  · cases represented with
    | value payload =>
      rw [outcomeEq]
      exact .value payload
    | fault matched =>
      rw [outcomeEq]
      exact .fault (semantic _ _ matched)
  · have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
      (bridge.pool initial) (bridge.pool reached) admitted.rows frame
    cases outcome with
    | value sourceValue =>
      refine ⟨rows, ?_⟩
      intro value same
      cases same
      have preserved := SelectedCompilationReadAdmission.read_preserved certificate unique lookup read
        cellRep.ordinary locals admitted.heap sourceTyped trace.sound.value_plain
      exact ⟨preserved.value_typed, preserved.heap_typed⟩
    | fault failure =>
      cases failure with
      | semantic reason => exact ⟨rows, by intro value same; cases same⟩
      | stage origin call reason => exact rows

include extension semantic unique in
/-- A completed native read reconstructs the original atomic Source outcome
at grade one. Lazy mapping initialization retains its exact written cell and
every caller row at the same final store. -/
theorem reflects_local [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    ReflectsAt bridge context model registry invocation
      (fun scope id lowered => reads scope id lowered ∧
        ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id)) faults size := by
  intro scope id lowered ⟨receipt, readFault⟩ node found sourceTyped
    mapping world administrative environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨certificate, typeEq, binding⟩ := receipt
  have nodeEq := Option.some.inj (certificate.metadata.found.symm.trans found)
  obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
  obtain ⟨_, selected, _, _, _, selectedRead, _, cellRep⟩ :=
    GenericHeap.lookup_visible environments heaps lookup certificate.slot
  have sameCell := read.functional selectedRead
  subst selected
  obtain ⟨outcome, after, sourceTrace, represented, finalHeaps, frame, metadata⟩ :=
    certificate.reflects functions extension program context invocation.evidence binding
      environments heaps locals agrees readFault (by simpa only [← typeEq] using completed.sound)
  simp only [SourceCoreCompatibleValues.Context.initial, nodeEq, typeEq] at represented finalHeaps
  have staged := staged_of_read (registry := registry) certificate unique lookup read cellRep.ordinary sourceTrace
  let transport := administrativeTransport headers keys
  let reachedPool := transport.extend (bridge.pool initial) (.refl _) (.refl _) frame metadata
  obtain ⟨reached, _poolEq, related⟩ := bridge.restore initial reachedPool (.refl _) (.refl _)
    frame metadata (transport.related (bridge.pool initial) (.refl _) (.refl _) frame metadata)
  refine ⟨Staging.Recursive.Size.stepSize [], _, after, mapping, world, staged, ?_, finalHeaps,
    .refl _, .refl _, frame, metadata, reached, related, ?_⟩
  · cases represented with
    | value payload => exact .value payload
    | fault matched => exact .fault (semantic _ _ matched)
  · have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
      (bridge.pool initial) (bridge.pool reached) admitted.rows frame
    cases outcome with
    | value sourceValue =>
      refine ⟨rows, ?_⟩
      intro value same
      cases same
      have preserved := SelectedCompilationReadAdmission.read_preserved certificate unique lookup read
        cellRep.ordinary locals admitted.heap sourceTyped staged.sound.value_plain
      exact ⟨preserved.value_typed, preserved.heap_typed⟩
    | fault reason => exact ⟨rows, by intro value same; cases same⟩

include extension uninitialized semantic unique in
/-- The global diagnostic interface follows by restricting it to the actual read. -/
theorem preserves [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    PreservesAt bridge context model registry invocation reads faults size := by
  intro scope id lowered receipt
  exact preserves_local bridge functions extension semantic unique size
    ⟨receipt, uninitialized scope id lowered receipt⟩

include extension uninitialized semantic unique in
/-- The global diagnostic interface follows by restricting it to the actual read. -/
theorem reflects [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    ReflectsAt bridge context model registry invocation reads faults size := by
  intro scope id lowered receipt
  exact reflects_local bridge functions extension semantic unique size
    ⟨receipt, uninitialized scope id lowered receipt⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationLiteralBounds
/-! Actual literal and group receipts preserve Source admission without
requiring the bodies of unrelated program declarations to be well typed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationLiteralBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CompatibleExpressionLiterals CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLiteralGroupBounds (Tree)
universe u

private theorem literal_value_typed {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {value : Dynamic.Value}
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment before
      node.form node.requirements node.coercions value after) :
    Dynamic.ValueHasType context after value node.type := by
  cases literal with
  | unit form type _ _ =>
      rw [form] at raw
      rw [type]
      cases raw with
      | tuple _ elements pack => cases elements; cases pack; exact .unit
  | bool value form type _ _ =>
      rw [form] at raw
      rw [type]
      cases raw
      exact .bool value
  | word value form type _ _ _ =>
      rw [form] at raw
      rw [type]
      cases raw with
      | literal _ constructs => exact constructs.hasType
  | resolvedWord form metadata | resolvedInteger form metadata =>
      rw [form] at raw
      cases raw with
      | integerLiteral _ constructs =>
          simpa only [metadata.nodeType, metadata.targetType] using constructs.hasType

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem atomic_not_local {form : ExpressionForm} (atomic : Atomic form) :
    ∀ name binder, form ≠ .reference name (.local binder) := by
  cases atomic <;> intros <;> intro impossible <;> cases impossible

private theorem literal_atomic {solved node type code} (literal : Literal solved node type code) : Atomic node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .bool _ _
  | word value form _ _ _ _ => rw [form]; exact .word _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integer _ _

private theorem literal_coercions {solved node type code} (literal : Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

private theorem evaluation_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (atomic : Atomic node.form) (empty : node.coercions = [])
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment before node.form node.requirements node.coercions value after := by
  cases evaluation with
  | intro found raw coercions =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact raw
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (atomic_not_local atomic _ _ form)

private theorem fault_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (atomic : Atomic node.form) (empty : node.coercions = [])
    (fault : Dynamic.ExpressionFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw => exact contains_unique unique found contains ▸ raw
  | coercion found _ failed =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (atomic_not_local atomic _ _ form)

private theorem literal_form_unique {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap firstHeap secondHeap : Dynamic.Heap}
    {left right : Dynamic.Value}
    (first : Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions left firstHeap)
    (second : Dynamic.ExpressionFormEvaluates program context evidence source environment heap node.form node.requirements node.coercions right secondHeap) :
    left = right ∧ firstHeap = secondHeap := by
  cases literal with
  | unit form _ _ _ =>
    rw [form] at first second
    cases first with | tuple _ elements pack =>
      cases elements
      cases pack
      cases second with | tuple _ elements pack => cases elements; cases pack; exact ⟨rfl, rfl⟩
  | bool value form _ _ _ => rw [form] at first second; cases first; cases second; exact ⟨rfl, rfl⟩
  | word value form _ _ _ _ =>
    rw [form] at first second
    cases first with | literal _ first =>
      cases second with | literal _ second => exact ⟨first.functional second, rfl⟩
  | resolvedWord form _ | resolvedInteger form _ =>
    rw [form] at first second
    cases first with | integerLiteral _ first =>
      cases second with | integerLiteral _ second => exact ⟨first.functional second, rfl⟩

private theorem literal_excludes_fault_with_evidence {solved : List SolvedRequirement} {node : ExpressionNode} {type code}
    (literal : Literal solved node type code)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : NumericEvidence context evidence node)
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after) : False := by
  cases literal with
  | unit form _ _ _ =>
    rw [form] at fault
    cases fault with | tuple _ failed => cases failed
  | bool value form _ _ _ | word value form _ _ _ _ => rw [form] at fault; cases fault
  | resolvedWord form metadata | resolvedInteger form metadata =>
    rw [form] at fault
    cases fault with | integerRequirement _ unavailable =>
      exact (valid _ _ form).2 unavailable


private theorem literal_atomic_staged {solved node type code}
    (literal : Literal solved node type code) : Staging.Recursive.AtomicForm node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .reference _ _
  | word value form _ _ _ _ => rw [form]; exact .literal _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integerLiteral _ _

/-- The actual atomic compiler forms cannot acquire a nested stage failure. -/
private theorem no_stage
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode} {size : Nat}
    {solved : List SolvedRequirement} {type code} {failedScope call reason}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (literal : Literal solved node type code)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context environment
      before id (.fault (.stage failedScope call reason)) after) : False := by
  have occurrence_atomic : ∀ {form requirements}, Staging.Recursive.Occurrence invocation id form requirements → Atomic form := by
    intro form requirements occurrence
    obtain ⟨actualNode, contains, sameForm, _requirements, _coercions⟩ := occurrence
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [← sameForm]
    exact (literal_atomic literal)
  cases trace with
  | generalizedLocal contains localForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      exact False.elim (atomic_not_local (literal_atomic literal) _ _ localForm)
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique found (literal_coercions literal) contains))
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorFault occurrence _ =>
      have atomic := occurrence_atomic occurrence
      cases atomic
  | tupleFault occurrence failed =>
      have atomic := occurrence_atomic occurrence
      cases atomic
      cases failed
  | group occurrence _
  | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unaryOperandFault occurrence _
  | binaryLeftFault occurrence _ | binaryRightFault occurrence _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | applied occurrence _ _ _ _ _ _ =>
      cases occurrence_atomic occurrence

variable {checked : SourceCoreCompatibleCatalog.Checked} {rawRegistry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique invocation.source)
  (faults : RecursiveStageMeaning.FaultRep)

private abbrev literalCertificate : GenericExpressionMeaning.Certificate :=
  fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate solved invocation.source id lowered

include sameLedger runtimeLedger unique in
/-- A genuine static numeric receipt constructs the actual Source and native
values. The Source grade is independent of native evaluation size. -/
theorem literal_preserves (size : Nat) :
    PreservesAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (literalCertificate (solved := solved) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨other, otherFound, literal, selected⟩ := receipt
  have same := Option.some.inj (otherFound.symm.trans found)
  cases same
  have valid := selected.evidence sameLedger runtimeLedger invocation.evidence
  obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
    literal.evaluates_with_evidence functions program context invocation.evidence valid invocation.source
      environment before mapping world actual store ξ
  have unchanged : outcome = .value sourceValue ∧ after = before := by
    cases outcome with
    | value value =>
        have actualRaw := evaluation_raw unique (lookupExpression?_sound found)
          (literal_atomic literal) (literal_coercions literal) trace.sound.value_plain
        obtain ⟨rfl, rfl⟩ := literal_form_unique literal actualRaw raw
        exact ⟨rfl, rfl⟩
    | fault failure =>
        cases failure with
        | semantic reason =>
            exact False.elim (literal_excludes_fault_with_evidence literal valid
              (fault_raw unique (lookupExpression?_sound found) (literal_atomic literal) (literal_coercions literal)
                trace.sound.semanticFault_plain))
        | stage failedScope call reason => exact False.elim (no_stage unique found literal trace)
  obtain ⟨rfl, rfl⟩ := unchanged
  refine ⟨.inRight .word coreValue, store, mapping, world, evaluated, .value represented,
    heaps, .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨literal_value_typed literal raw, admitted.heap⟩⟩

include sameLedger runtimeLedger in
/-- Reflection constructs an atomic Source rule of grade one and keeps the
literal input caller itself as the reached dependent witness. -/
theorem literal_reflects (size : Nat) :
    ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (literalCertificate (solved := solved) (invocation := invocation)) faults size := by
  intro scope id lowered receipt node found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨other, otherFound, literal, selected⟩ := receipt
  have same := Option.some.inj (otherFound.symm.trans found)
  cases same
  have valid := selected.evidence sameLedger runtimeLedger invocation.evidence
  obtain ⟨sourceValue, coreValue, raw, represented, evaluated⟩ :=
    literal.evaluates_with_evidence functions program context invocation.evidence valid invocation.source
      environment before mapping world actual store ξ
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed.sound
  have sourceTrace : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [])
      invocation context environment before id (.value sourceValue) before :=
    .atomicValue (lookupExpression?_sound found) (literal_atomic_staged literal) (literal_coercions literal)
      (by simpa only [(literal_coercions literal)] using raw)
  refine ⟨Staging.Recursive.Size.stepSize [], .value sourceValue, before, mapping, world,
    sourceTrace, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _,
    initial, callerProtocol.refl initial, ?_⟩
  exact ⟨admitted.rows, by
    intro value same
    cases same
    exact ⟨literal_value_typed literal raw, admitted.heap⟩⟩

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

include sameLedger runtimeLedger unique in
/-- Finite structural descent closes every supported node. There is no
universal E law or literal execution supplied by the caller. -/
theorem preserves (size : Nat) :
    PreservesAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree generalizing size with
  | literal receipt =>
      exact literal_preserves functions bridge sameLedger runtimeLedger unique faults size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
      have children : PreservesBelow bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)

include sameLedger runtimeLedger unique in
/-- Group reflection invokes only its finite child at the SAME native size.
The reconstructed Source grade grows through the independent group rule. -/
theorem reflects (size : Nat) :
    ReflectsAt bridge context (CompatibleAmbientHeap.payloadModel checked rawRegistry functions)
      registry invocation (Tree checked solved invocation.source) faults size := by
  intro scope id lowered tree
  induction tree with
  | literal receipt =>
      exact literal_reflects functions bridge sameLedger runtimeLedger faults size receipt
  | @group id node inner innerNode lowered metadata form innerFound sourceType child ih =>
      have children : ReflectsAt bridge context
          (CompatibleAmbientHeap.payloadModel checked rawRegistry functions) registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationLiteralBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPairBounds
/-! Pair results inherit typing and heap admission from the actual ordered
children, including callable values and their complete captures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPairBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open GenericExpressionMeaning (agree_prefix rename_prefix)
open CompatibleExpressionProducts (Metadata)
open CallableIndexedOwnedPreparedStagedPairBounds (Pair ProductValues)
universe u

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

/-- A payload model may combine two represented values at the same reached
heap/world. This is a representation constructor, with no execution input. -/
private inductive SourceChildren (size : Nat) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) :
    Staging.Recursive.Outcome → Dynamic.Heap → Prop where
  | leftFault {childSize after failure}
      (smaller : childSize < size)
      (child : Staging.Recursive.Size.Expression program registry childSize invocation context
        environment before left (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | rightFault {firstSize secondSize middle after value failure}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value value) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.fault failure) after) :
      SourceChildren size environment before left right (.fault failure) after
  | values {firstSize secondSize middle after leftValue rightValue}
      (firstSmaller : firstSize < size) (secondSmaller : secondSize < size)
      (first : Staging.Recursive.Size.Expression program registry firstSize invocation context
        environment before left (.value leftValue) middle)
      (second : Staging.Recursive.Size.Expression program registry secondSize invocation context
        environment middle right (.value rightValue) after) :
      SourceChildren size environment before left right (.value (.product leftValue rightValue)) after

private theorem source_children
    {id left right : ExpressionId} {node : ExpressionNode}
    {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .tuple [left, right])
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    SourceChildren (program := program) (registry := registry) (invocation := invocation)
      (context := context) size environment before left right outcome after := by
  have same_node : ∀ {actualNode}, ContainsExpression invocation.source id actualNode → actualNode = node := by
    intro actualNode contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  have occurrence_form : ∀ {actualForm requirements},
      Staging.Recursive.Occurrence invocation id actualForm requirements → actualForm = .tuple [left, right] := by
    intro actualForm requirements occurrence
    obtain ⟨actualNode, contains, actualFormEq, _requirements, _coercions⟩ := occurrence
    exact actualFormEq.symm.trans ((congrArg ExpressionNode.form (same_node contains)).trans form)
  cases trace with
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have actualForm := (congrArg ExpressionNode.form (same_node contains)).trans form
      rw [actualForm] at atomic
      cases atomic
  | generalizedLocal contains localForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains localForm _ _ _ _ _ _ _ =>
      cases same_node contains
      rw [form] at localForm
      cases localForm
  | pair occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .values (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | pairLeftFault occurrence child =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .leftFault (Staging.Recursive.Size.child_lt_stepSize (by simp)) child
  | pairRightFault occurrence first second =>
      have ids := ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases List.cons.inj ids with | intro leftEq rest =>
        cases leftEq
        cases (List.cons.inj rest).1
        exact .rightFault (Staging.Recursive.Size.child_lt_stepSize (by simp))
          (Staging.Recursive.Size.child_lt_stepSize (by simp)) first second
  | tupleValue occurrence sequence packed =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail
              cases packed with
              | cons last =>
                  cases last
                  exact .values (by simp [Staging.Recursive.Size.stepSize]; omega)
                    (by simp [Staging.Recursive.Size.stepSize]; omega) first second
  | tupleFault occurrence sequence =>
      cases ExpressionForm.tuple.inj (occurrence_form occurrence)
      cases sequence with
      | headFault first =>
          exact .leftFault (by simp [Staging.Recursive.Size.stepSize]; omega) first
      | tailFault first rest =>
          cases rest with
          | headFault second =>
              exact .rightFault (by simp [Staging.Recursive.Size.stepSize]; omega)
                (by simp [Staging.Recursive.Size.stepSize]; omega) first second
          | tailFault _ rest => cases rest
  | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _
  | constructorValue occurrence _ _ | constructorFault occurrence _
  | group occurrence _
  | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _
  | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _
  | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | binaryPanic occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ => cases occurrence_form occurrence

private theorem child_typing
    {id left right : ExpressionId} {node leftNode rightNode : ExpressionNode} {type : Ty}
    (metadata : Metadata checked invocation.source id node type)
    (form : node.form = .tuple [left, right])
    (leftFound : invocation.source.lookupExpression? left = some leftNode)
    (rightFound : invocation.source.lookupExpression? right = some rightNode)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ExpressionHasType invocation.source context left leftNode.type ∧
      ExpressionHasType invocation.source context right rightNode.type := by
  obtain ⟨first, second, firstFound, secondFound, _sourceType, firstTyped, secondTyped⟩ :=
    CompatibleExpressionProducts.pair_source_types unique metadata.found form metadata.coercions typed
  cases Option.some.inj (firstFound.symm.trans leftFound)
  cases Option.some.inj (secondFound.symm.trans rightFound)
  exact ⟨firstTyped, secondTyped⟩

/-- Two genuine Source children are executed in their actual successive heaps.
Either failure keeps its original scoped representation and exact endpoint. -/
theorem pair_preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : PreservesBelow bridge context model registry invocation children faults budget) :
    ∀ size, size ≤ budget → PreservesAt bridge context model registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have parts := source_children unique metadata.found form trace
      cases parts with
      | leftFault smaller first =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le smaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | fault matched =>
              refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
                maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
              rw [DataExpressionSequence.pair_rename]
              exact LocalSequence.pair_left_failure _ _ evaluated
      | rightFault firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps,
                  maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 second
              cases represented with
              | fault matched =>
                  refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related,
                    post.at_fault_type⟩
                  rw [DataExpressionSequence.pair_rename]
                  rw [rename_prefix] at secondEval
                  exact LocalSequence.pair_right_failure _ _ firstEval secondEval
      | values firstSmaller secondSmaller first second =>
          obtain ⟨value, middleStore, middleMap, middleWorld, firstEval, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (Nat.lt_of_lt_of_le firstSmaller within) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              obtain ⟨value, finalStore, finalMap, finalWorld, secondEval, represented, finalHeaps,
                  maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                childMeaning _ (Nat.lt_of_lt_of_le secondSmaller within) secondChild rightFound secondTyped
                  (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                  (agree_prefix agrees _) (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                  middleState firstPost.at_value.2 second
              cases represented with
              | @value lastSource lastCoreValue lastPayload =>
                  refine ⟨.inRight .word (.pair coreValue lastCoreValue), finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
                    firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                    firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related, ?_⟩
                  · rw [DataExpressionSequence.pair_rename]
                    rw [rename_prefix] at secondEval
                    exact LocalSequence.pair_success _ _ firstEval secondEval
                  · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                  · refine ⟨post.rows, ?_⟩
                    intro value same
                    cases same
                    refine ⟨?_, post.at_value.2.heap⟩
                    rw [sourceType]
                    exact .product (firstPost.at_value.1.mono heapMetadata) post.at_value.1

/-- Actual native bind inversion supplies strictly smaller executed children;
the Source pair grade is constructed independently from their Source traces. -/
theorem pair_reflects
    (unique : NodeOccurrencesUnique invocation.source)
    (products : ProductValues (model := model)) (budget : Nat)
    (childMeaning : ReflectsBelow bridge context model registry invocation children faults budget) :
    ∀ size, size ≤ budget → ReflectsAt bridge context model registry invocation
      (Pair checked invocation.source children) faults size := by
  intro size within scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  cases certified with
  | actual metadata form leftFound rightFound sourceType firstChild secondChild =>
      cases Option.some.inj (found.symm.trans metadata.found)
      obtain ⟨firstTyped, secondTyped⟩ := child_typing metadata form leftFound rightFound unique typed
      have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [_, _]) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      change EvaluationSize size actual store ((LocalSequence.pair _ _ _ _).rename ξ) value finalStore at completed
      rw [DataExpressionSequence.pair_rename] at completed
      have complete := completed
      cases completed with
      | caseLeft first _ =>
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
              maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            childMeaning _ (by omega) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | fault matched =>
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                (LocalSequence.pair_left_failure _ _ first.sound)
              exact ⟨_, .fault _, after, finalMap, finalWorld, .pairLeftFault occurrence trace,
                .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related,
                post.at_fault_type⟩
      | caseRight first continuation =>
          obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
              firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
            childMeaning _ (by omega) firstChild leftFound firstTyped
              environments heaps locals agrees actualTyped initial admitted first
          cases represented with
          | @value sourceValue coreValue payload =>
              cases continuation with
              | caseLeft second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
                      maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                    childMeaning _ (by omega) secondChild rightFound secondTyped
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                      (agree_prefix agrees _)
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted
                  cases represented with
                  | fault matched =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_right_failure _ _ first.sound second.sound)
                      exact ⟨_, .fault _, after, finalMap, finalWorld,
                        .pairRightFault occurrence firstTrace secondTrace, .fault matched,
                        finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                        firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related,
                        post.at_fault_type⟩
              | caseRight second _ =>
                  have shifted := second
                  rw [← rename_prefix] at shifted
                  obtain ⟨lastSize, outcome, after, finalMap, finalWorld, secondTrace, represented, finalHeaps,
                      maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
                    childMeaning _ (by omega) secondChild rightFound secondTyped
                      (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                      (agree_prefix agrees _)
                      (.cons (model.runtime_hasType payload) (actualTyped.weaken firstWorlds))
                      middleState firstPost.at_value.2 shifted
                  cases represented with
                  | @value lastSource lastCoreValue lastPayload =>
                      obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound
                        (LocalSequence.pair_success _ _ first.sound second.sound)
                      have trace := Staging.Recursive.Size.Expression.pair occurrence firstTrace secondTrace
                      refine ⟨_, .value _, after, finalMap, finalWorld, trace, ?_, finalHeaps,
                        firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
                        firstMetadata.trans heapMetadata, reached, callerProtocol.trans firstRelated related, ?_⟩
                      · exact .value (sourceType ▸ products (model.extend payload maps worlds) lastPayload)
                      · refine ⟨post.rows, ?_⟩
                        intro value same
                        cases same
                        refine ⟨?_, post.at_value.2.heap⟩
                        rw [sourceType]
                        exact .product (firstPost.at_value.1.mono heapMetadata) post.at_value.1

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPairBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadProductBounds
/-! One accepted compiler extraction retains the actual finite literal/read/
group/pair tree and its selected literal sites. Structural recursion constructs
every staged child meaning internally, including ordinary local reads and lazy
mapping initialization at the actual reached state. Source and native grades
remain independent: transparent group reflection uses the same native grade,
while evaluated pair binds use their real strict child grades. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadProductBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u
open CallableLambdaBodyReachability

open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  {semanticFaults : FunctionCalls.FaultRep}
  (faults : RecursiveStageMeaning.FaultRep)
  (uninitialized : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ scope id lowered,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt scope id lowered →
    Reaches invocation.source [.expression faultRoot] (.expression id) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt id))
  (semantic : ∀ reason token, semanticFaults reason token → faults (.semantic reason) token)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Certificate readFuel
  (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  invocation.source context solved reasonAt

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private def Two (scope : SourceCoreLocalCell.Scope) (left right : ExpressionId)
    (first second : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧
    ((child = left ∧ code = first) ∨ (child = right ∧ code = second))

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues
      (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include extension sameLedger runtimeLedger uninitializedOn semantic unique in
/-- LiteralSites recursion proves each actual Source child internally. A read
uses its genuine local certificate; no read or whole-child meaning is supplied. -/
theorem preserves_reached [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    PreservesAt bridge context valueModel registry invocation
      (fun scope id lowered => trees scope id lowered ∧
        Reaches invocation.source [.expression faultRoot] (.expression id)) faults size := by
  intro scope id lowered ⟨⟨tree, sites⟩, reached⟩
  revert reached
  induction sites generalizing size with
  | literal _ receipt =>
      intro _reached actualNode
      exact SelectedCompilationLiteralBounds.literal_preserves
        functions bridge sameLedger runtimeLedger unique faults size receipt
  | read receipt =>
      intro reached actualNode
      exact SelectedCompilationReadBounds.preserves_local bridge functions extension
        semantic unique size ⟨receipt, uninitializedOn scope _ _ receipt reached⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      intro reached
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : PreservesBelow bridge context valueModel registry invocation
          (Point scope inner lowered) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih childSize innerReached
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size children
        size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      intro reached
      have leftReached : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : PreservesBelow bridge context valueModel registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize leftReached
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize rightReached
      intro actualNode
      exact SelectedCompilationPairBounds.pair_preserves bridge unique (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension sameLedger runtimeLedger uninitializedOn semantic unique in
/-- Reflection follows the same finite sites at independent native grades.
Grouping recurses at the same grade; actual pair binds supply strict children. -/
theorem reflects_reached [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    ReflectsAt bridge context valueModel registry invocation
      (fun scope id lowered => trees scope id lowered ∧
        Reaches invocation.source [.expression faultRoot] (.expression id)) faults size := by
  intro scope id lowered ⟨⟨tree, sites⟩, reached⟩
  revert reached
  induction sites generalizing size with
  | literal _ receipt =>
      intro _reached actualNode
      exact SelectedCompilationLiteralBounds.literal_reflects
        functions bridge sameLedger runtimeLedger faults size receipt
  | read receipt =>
      intro reached actualNode
      exact SelectedCompilationReadBounds.reflects_local bridge functions extension
        semantic unique size ⟨receipt, uninitializedOn scope _ _ receipt reached⟩
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
      intro reached
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : ReflectsAt bridge context valueModel registry invocation
          (Point scope inner lowered) faults size := by
        intro current child code point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih size innerReached
      intro actualNode
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size children
        (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
      intro reached
      have leftReached : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have rightReached : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have children : ReflectsBelow bridge context valueModel registry invocation
          (Two scope left right first second) faults size := by
        intro childSize _smaller current child code point
        obtain ⟨rfl, alternative⟩ := point
        cases alternative with
        | inl left => obtain ⟨rfl, rfl⟩ := left; exact leftIH childSize leftReached
        | inr right => obtain ⟨rfl, rfl⟩ := right; exact rightIH childSize rightReached
      intro actualNode
      exact SelectedCompilationPairBounds.pair_reflects bridge unique (product_values functions) size children size (Nat.le_refl _)
        (.actual metadata form leftFound rightFound sourceType
          ⟨rfl, .inl ⟨rfl, rfl⟩⟩ ⟨rfl, .inr ⟨rfl, rfl⟩⟩)

include extension sameLedger runtimeLedger uninitialized semantic unique in
/-- Global diagnostic facts restrict to each authentic expression root. -/
theorem preserves [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    PreservesAt bridge context valueModel registry invocation trees faults size := by
  intro scope id lowered tree
  exact preserves_reached (faultRoot := id) bridge functions extension sameLedger runtimeLedger faults
    (fun current child code receipt _reached => uninitialized current child code receipt)
    semantic unique size ⟨tree, .root (by simp)⟩

include extension sameLedger runtimeLedger uninitialized semantic unique in
/-- Global diagnostic facts restrict to each authentic expression root. -/
theorem reflects [FunctionCalls.FaultTokens semanticFaults] (size : Nat) :
    ReflectsAt bridge context valueModel registry invocation trees faults size := by
  intro scope id lowered tree
  exact reflects_reached (faultRoot := id) bridge functions extension sameLedger runtimeLedger faults
    (fun current child code receipt _reached => uninitialized current child code receipt)
    semantic unique size ⟨tree, .root (by simp)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationReadProductBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationConstructorBounds
/-! Nominal construction uses the actual metadata header and ordered recursive
children. A reached child failure keeps its original scope and heap; successful
construction retains the same caller state and the exact constructor payload. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationConstructorBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionConstructors (construct_rename construct_success construct_failure)
universe u

open CallableIndexedOwnedPreparedStagedConstructorHeadBounds (Point)

private theorem valuesRep {values : SourceCoreCompatibleValues.Context} {receiving : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {functions : FunctionModel values.checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {types : List TypeSystem.Ty} {natives : List Ty}
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values (CompatibleAmbientHeap.payloadModel values.checked receiving functions)
      mapping world types natives sources payloads) :
    ValuesRep values.checked receiving functions mapping world types sources payloads natives := by
  induction represented with
  | nil => exact .nil
  | cons head tail ih => exact .cons head ih

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (runtime : Dynamic.SourceRuntimeValid program context invocation.source)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions
local notation "valuesContext" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked

include bridge functions extension faults unique runtime in
theorem constructor_preserves {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId} {tag : ConstructorId}
    {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (size : Nat) (childMeaning : PreservesBelow bridge context model registry invocation children faults size)
    (receipt : CompatibleExpressionConstructors.Header valuesContext invocation.source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation)
    (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
    (_count : ids.length = instantiation.payloadTypes.length)
    (_nodes : CompatibleExpressionConstructors.Nodes invocation.source ids instantiation.payloadTypes codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes) :
    PreservesAt bridge context model registry invocation
      (Point scope id ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  have valid := CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges
  obtain ⟨_admissible, typing, sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique receipt.metadata.found form receipt.metadata.coercions typed
  rcases CallableIndexedOwnedPreparedStagedConstructorSourceInversion.children unique receipt.metadata.found form trace with
    ⟨sequenceSize, sources, sameSize, outcomeEq, sourceTrace⟩ |
    ⟨sequenceSize, failure, sameSize, outcomeEq, sourceTrace⟩
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, payloads, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_values bridge size sequence unique typing
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace within
    refine ⟨.inRight .word (.constructed tag (.pair (.word header) (packValues values))), finalStore, finalMap, finalWorld,
      ?_, ?_, finalHeaps, maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [construct_rename]
      exact construct_success tag header evaluated
    · rw [receipt.sourceType]
      exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registryOwner)
        receipt.selected (receipt.sourceType ▸ receipt.metadata.projected) receipt.registered (valuesRep (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) payloads))
    · refine ⟨post.rows, ?_⟩
      intro value same
      cases same
      exact ⟨sourceType ▸ .constructed valid post.values_typed, post.at_values.heap⟩
  · subst outcome
    have within : sequenceSize ≤ size := Nat.le_of_lt (by
      rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      SelectedCompilationExpressionSequence.preserves_fault bridge size sequence unique typing
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace within
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [construct_rename]
      exact construct_failure tag header evaluated
    · exact post.fault

include bridge functions extension faults unique runtime in
theorem constructor_reflects {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId} {tag : ConstructorId}
    {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (size : Nat) (childMeaning : ReflectsBelow bridge context model registry invocation children faults size)
    (receipt : CompatibleExpressionConstructors.Header valuesContext invocation.source id node instantiation tag header codes)
    (form : node.form = .constructor instantiation ids)
    (admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation)
    (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
    (_count : ids.length = instantiation.payloadTypes.length)
    (_nodes : CompatibleExpressionConstructors.Nodes invocation.source ids instantiation.payloadTypes codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes) :
    ReflectsAt bridge context model registry invocation
      (Point scope id ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩)
      faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  have valid := CompatibleSourceInstantiationClosure.constructor_valid admissible runtime.variables_closed ranges
  obtain ⟨_admissible, typing, sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique receipt.metadata.found form receipt.metadata.coercions typed
  rw [construct_rename] at completed
  obtain ⟨sequenceSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique typing childMeaning
      environments heaps locals agrees actualTyped initial admitted childEvaluation smaller
  have occurrence : Staging.Recursive.Occurrence invocation child (.constructor instantiation ids) :=
    ⟨node, lookupExpression?_sound receipt.metadata.found, form, receipt.metadata.requirements, receipt.metadata.coercions⟩
  cases represented with
  | @values sources values payloads =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (construct_success tag header childEvaluation.sound)
      have trace := Staging.Recursive.Size.Expression.constructorValue occurrence valid sourceTrace
      refine ⟨_, _, after, finalMap, finalWorld, trace, ?_, finalHeaps,
        maps, worlds, frame, metadata, reached, related, ?_⟩
      · rw [receipt.sourceType]
        exact .value (.constructed (receipt.original.extend extension) (extension.signatures.trans (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registryOwner)
          receipt.selected (receipt.sourceType ▸ receipt.metadata.projected) receipt.registered (valuesRep (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) payloads))
      · refine ⟨post.rows, ?_⟩
        intro value same
        cases same
        exact ⟨sourceType ▸ .constructed valid post.values_typed, post.at_values.heap⟩
  | fault matched =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (construct_failure tag header childEvaluation.sound)
      have trace := Staging.Recursive.Size.Expression.constructorFault occurrence sourceTrace
      exact ⟨_, _, after, finalMap, finalWorld, trace, .fault matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related,
        post.fault⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationConstructorBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationTupleBounds
/-! Generic admitted tuple heads retain the actual ordered child certificate
vector. The original Source inversion, legacy binary pair rules and reached
state proofs supply the head semantics. Child hypotheses are theorem arguments;
static compiler receipts carry no execution law. Singleton reflection permits
the same native grade and constructs its independent Source grade. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationTupleBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

private def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

private theorem occurrence_form {invocation : Staging.Recursive.Scope} {id : ExpressionId}
    {node : ExpressionNode} {form : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (owned : Staging.Recursive.Occurrence invocation id form requirements) : node.form = form := by
  obtain ⟨other, contains, formed, _, _⟩ := owned
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst other
  exact formed

/-- Outside the two-element legacy rules, the actual list grade is bounded
by the original Source parent. The empty atomic tuple is childless. -/
private theorem source_sequence {program : Program} {registry : Staging.Recursive.Registry}
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {checked : SourceCoreCompatibleCatalog.Checked} {id : ExpressionId} {node : ExpressionNode}
    {type : Core.Ty} {ids : List ExpressionId} {size : Nat}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Staging.Recursive.Outcome}
    (metadata : CompatibleExpressionPrimitives.Metadata checked invocation.source id node type)
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique invocation.source)
    (notPair : ids.length ≠ 2)
    (trace : Staging.Recursive.Size.Expression program registry size invocation context
      environment before id outcome after) :
    ∃ childSize sequence, childSize ≤ size ∧
      Staging.Recursive.Size.Expressions program registry childSize invocation context
        environment before ids sequence after ∧
      RecursiveStageTupleMeaning.PacksOutcome sequence outcome := by
  cases trace with
  | coercedValue contains nonempty _ _ | coercedFault contains nonempty _ =>
      exact False.elim (nonempty (CallableIndexedOwnedPreparedStagedCoercionExclusion.empty_at unique metadata.found metadata.coercions contains))
  | atomicValue contains atomic uncoerced raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      subst node
      rw [form] at atomic raw
      cases atomic
      cases raw with
      | tuple _ children pack =>
          cases children
          cases pack
          exact ⟨_, _, Nat.le_refl _, .nil, .values .nil⟩
  | atomicFault contains atomic uncoerced raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      subst node
      rw [form] at atomic raw
      cases atomic
      cases raw with | tuple _ children => cases children
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans metadata.found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | pair owned first second =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | pairLeftFault owned child =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | pairRightFault owned first failed =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      simp at notPair
  | tupleValue owned children pack =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      exact ⟨_, _, Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)), children, .values pack⟩
  | tupleFault owned children =>
      have same := ExpressionForm.tuple.inj (form.symm.trans (occurrence_form unique metadata.found owned))
      subst ids
      exact ⟨_, _, Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp)), children, .fault _⟩
  | indexBaseFault owned _ | indexKeyFault owned _ _ | indexResult owned _ _ _ | builtinArgumentsFault owned _ | builtinApplied owned _ _ | directArgumentsFault owned _ _ | directApplied owned _ _ _ _ _
  | constructorValue owned _ _ | constructorFault owned _
  | group owned _
  | unaryMethod owned _ _ _ _ _ _ _ _ _ | binaryMethod owned _ _ _ _ _ _ _ _ _ _ _
  | unary owned _ _ | unaryOperandFault owned _ | unaryInvalid owned _ _
  | binaryLeftFault owned _ | binaryLeftInvalid owned _ _
  | binaryShortCircuit owned _ _ | binaryRightFault owned _ _ _
  | binary owned _ _ _ _ | binaryInvalid owned _ _ _ _ | binaryPanic owned _ _ _ _
  | conditional owned _ _ | conditionalFault owned _
  | calleeFault owned _ | notCallable owned _ _ | rejected owned _ _
  | argumentsFault owned _ _ _ | sourceArity owned _ _ _ _
  | applied owned _ _ _ _ _ _ =>
      have impossible := form.symm.trans (occurrence_form unique metadata.found owned)
      cases impossible

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "valuesContext" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked

private theorem product_values :
    CallableIndexedOwnedPreparedStagedPairBounds.ProductValues (model := valueModel) := by
  intro mapping world leftType rightType left right first second firstType secondType firstValue secondValue
  exact .product firstValue secondValue

include unique in
private theorem nonpair_preserves {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {node : ExpressionNode} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {children : GenericExpressionMeaning.Certificate}
    (header : CompatibleExpressionTuples.Header valuesContext invocation.source id node ids types codes)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids types codes)
    (notPair : ids.length ≠ 2) (size : Nat)
    (childMeaning : PreservesBelow bridge context valueModel registry invocation children faults size) :
    PreservesAt bridge context valueModel registry invocation
      (Point scope id (SourceCoreCalls.packArguments codes)) faults size := by
  intro current child lowered point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique header.metadata.found header.form header.metadata.coercions typed
  obtain ⟨childSize, sourceOutcome, within, childTrace, packed⟩ :=
    source_sequence header.metadata header.form unique notPair trace
  cases packed with
  | @values sources sourceValue sourcePack =>
      obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, relatedValues, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        SelectedCompilationExpressionSequence.preserves_values bridge size sequence unique typing
          childMeaning environments heaps locals agrees actualTyped initial admitted childTrace within
      have represented : RecursiveStageArguments.ResultFor valueModel finalMap finalWorld types codes faults
          (.values sources) (.inRight .word (packValues values)) := .values relatedValues
      obtain ⟨result, packed, payload⟩ := RecursiveStageTupleMeaning.sequence_result represented
      have same := (RecursiveStageTupleMeaning.PacksOutcome.values sourcePack).functional packed
      cases same
      refine ⟨_, finalStore, finalMap, finalWorld, evaluated, ?_, finalHeaps, maps, worlds, frame,
        metadata, reached, related, ?_⟩
      · simpa only [header.sourceType] using payload
      · refine ⟨post.rows, ?_⟩
        intro value same
        cases same
        exact ⟨header.sourceType ▸ sourcePack.hasType post.values_typed, post.at_values.heap⟩
  | fault failure =>
      obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        SelectedCompilationExpressionSequence.preserves_fault bridge size sequence unique typing
          childMeaning environments heaps locals agrees actualTyped initial admitted childTrace within
      exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related,
        post.fault⟩

include unique in
/-- Ordered tuple preservation consumes only the actual strict Source child
hypothesis. The binary legacy rules use the genuine pair producer. -/
theorem tuple_preserves {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (childMeaning : PreservesBelow bridge context valueModel registry invocation children faults size) :
    PreservesAt bridge context valueModel registry invocation
      (CompatibleExpressionTuples.Certificate valuesContext invocation.source children) faults size := by
  intro scope id lowered certified
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  cases sequence with
  | nil =>
      intro actualNode
      exact nonpair_preserves bridge functions faults unique
        header .nil (by simp) size childMeaning ⟨rfl, rfl, rfl⟩
  | single childFound generated =>
      intro actualNode
      exact nonpair_preserves bridge functions faults unique
        header (.single childFound generated) (by simp) size childMeaning ⟨rfl, rfl, rfl⟩
  | cons firstFound firstChild tail =>
      cases tail with
      | single secondFound secondChild =>
          intro actualNode
          exact SelectedCompilationPairBounds.pair_preserves bridge unique (product_values functions) size childMeaning size (Nat.le_refl _)
            (.actual header.metadata header.form firstFound secondFound header.sourceType firstChild secondChild)
      | cons nextFound nextChild rest =>
          intro actualNode
          exact nonpair_preserves bridge functions faults unique
            header (.cons firstFound firstChild (.cons nextFound nextChild rest)) (by simp) size
            childMeaning ⟨rfl, rfl, rfl⟩

include unique in
/-- Singleton reflection permits the same native child grade. Every branch
retains the exact recursive failure and actual reached caller state. -/
theorem tuple_reflects {children : GenericExpressionMeaning.Certificate} (size : Nat)
    (childMeaning : ReflectsBelow bridge context valueModel registry invocation children faults (size + 1)) :
    ReflectsAt bridge context valueModel registry invocation
      (CompatibleExpressionTuples.Certificate valuesContext invocation.source children) faults size := by
  intro scope id lowered certified actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨node, ids, types, codes, emitted, header, sequence⟩ := certified
  subst lowered
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨originalTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique header.metadata.found header.form header.metadata.coercions typed
  obtain ⟨sourceSize, sourceOutcome, after, finalMap, finalWorld, childTrace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge (size + 1) sequence unique typing
      childMeaning environments heaps locals agrees actualTyped initial admitted completed (Nat.lt_succ_self _)
  obtain ⟨outcome, packed, payload⟩ := RecursiveStageTupleMeaning.sequence_result represented
  have occurrence : Staging.Recursive.Occurrence invocation id (.tuple ids) :=
    ⟨actualNode, lookupExpression?_sound header.metadata.found, header.form,
      header.metadata.requirements, header.metadata.coercions⟩
  have trace : Staging.Recursive.Size.Expression program registry (Staging.Recursive.Size.stepSize [sourceSize])
      invocation context environment before id outcome after := by
    cases packed with
    | values pack => exact .tupleValue occurrence childTrace pack
    | fault failure => exact .tupleFault occurrence childTrace
  refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps, maps, worlds, frame,
    metadata, reached, related, ?_⟩
  · simpa only [header.sourceType] using payload
  · cases packed with
    | values pack =>
        refine ⟨post.rows, ?_⟩
        intro value same
        cases same
        exact ⟨header.sourceType ▸ pack.hasType post.values_typed, post.at_values.heap⟩
    | fault failure => exact post.fault

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationTupleBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorBounds
/-! Recursive staged operators consume their actual child caller witnesses.
Pure operator steps keep that state; the right operand or selected branch starts
at the first successful child's exact heap and admission. Both fault kinds pass
through unchanged. Static heads contain only compiler fields and children. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CompatibleExpressionPrimitives CompatibleExpressionConditionals
open ProtectedStateExpressionOperandTyping
universe u
open CallableIndexedOwnedPreparedStagedOperatorBounds (Head)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

private theorem unary_result_typed {operator : Syntax.UnaryOp} {operand result : TypeSystem.Ty}
    {core : UnaryOp} {source : Dynamic.Value} {value : Value} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} (profile : UnaryProfile operator operand result core)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world result source value core.resultType) :
    Dynamic.ValueHasType context heap source result := by
  cases profile
  all_goals first
    | obtain ⟨flag, rfl, _⟩ := bool_fields represented; exact .bool flag
    | obtain ⟨word, rfl, _⟩ := word_fields represented; exact .word word
    | obtain ⟨integer, rfl, _⟩ := integer_fields represented; exact .integer integer

private theorem binary_result_typed {operator : Syntax.BinaryOp} {operand result : TypeSystem.Ty}
    {mode : Mode} {source : Dynamic.Value} {value : Value} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep compiled.compatible.checked registry functions mapping world result source value (mode.resultType operator)) :
    Dynamic.ValueHasType context heap source result := by
  cases profile with
  | word strict => cases strict <;> first
    | obtain ⟨flag, rfl, _⟩ := bool_fields represented; exact .bool flag
    | obtain ⟨word, rfl, _⟩ := word_fields represented; exact .word word
  | integer strict => cases strict <;> first
    | obtain ⟨flag, rfl, _⟩ := bool_fields represented; exact .bool flag
    | obtain ⟨integer, rfl, _⟩ := integer_fields represented; exact .integer integer
  | panicking panicking => cases panicking <;> first
    | obtain ⟨word, rfl, _⟩ := word_fields represented; exact .word word
  | fixedComparison kind => cases kind <;>
    (obtain ⟨flag, rfl, _⟩ := bool_fields represented; exact .bool flag)
  | fixedBitwise kind =>
    obtain ⟨word, rfl, _, _, canonical⟩ := fixed_fields represented rfl
    exact .fixed word canonical
  | logicalAnd | logicalOr =>
    obtain ⟨flag, rfl, _⟩ := bool_fields represented
    exact .bool flag

private theorem successful {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    {type : TypeSystem.Ty} {value : Dynamic.Value}
    (typed : Dynamic.ValueHasType context index.heap value type)
    (admitted : Admission bridge context reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type (.value value) reached :=
  ⟨admitted.rows, by intro actual same; cases same; exact ⟨typed, admitted.heap⟩⟩

/-- A panic after both operands keeps the rows of the right operand's post. -/
private theorem panicked {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    {operandType type : TypeSystem.Ty} {value : Dynamic.Value} {code : UInt8}
    (post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context operandType (.value value) reached) :
    CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context type
      (.fault (.semantic (.panic code))) reached :=
  ⟨post.rows, by intro actual same; cases same⟩

/-- Strict Source children preserve the exact staged result and owned state. -/
theorem preserves_at [RecursiveStageMeaning.FaultTokens faults] (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (meaning : PreservesBelow bridge context model stages invocation certificate faults budget) :
    PreservesAt bridge context model stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  intro scope id lowered tree root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  have raw : ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context root.type outcome reached := by
    cases tree with
    | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have ih := fun n (bound : n < budget) => @meaning n bound _ _ _ child _ childFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change operand ∈ [operand]; simp) childFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.unary_inv metadata form unique trace
      cases sourceStep with
      | value childTrace applied childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨sourceResult, result, actualApplied, coreApplied, resultRep⟩ := profile.preserves payload
          have same := actualApplied.functional applied
          subst sourceResult
          refine ⟨.inRight .word result, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related, successful bridge (outputType ▸ unary_result_typed functions profile resultRep) post.at_value.2⟩⟩
          · rw [unary_rename]; exact LocalPrimitiveResults.unary_success evaluated coreApplied
          · exact .value (outputType ▸ resultRep)
      | fault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [unary_rename]; exact LocalPrimitiveResults.unary_failure evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
      | invalid childTrace failed childSmaller =>
        obtain ⟨_, _, _, _, _, represented, _⟩ := ih _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨_, _, applied, _, _⟩ := profile.preserves payload
          exact False.elim (failed.excludes_application ⟨_, applied⟩)
    | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have leftIH := fun n (bound : n < budget) => @meaning n bound _ _ _ leftTree _ leftFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change left ∈ [left, right]; simp) leftFound)
      have rightIH := fun n (bound : n < budget) => @meaning n bound _ _ _ rightTree _ rightFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change right ∈ [left, right]; simp) rightFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.binary_inv metadata form unique trace
      cases sourceStep with
      | leftFault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact mode.left_failure operator evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
      | leftInvalid childTrace invalid childSmaller =>
        obtain ⟨_, _, _, _, _, represented, _⟩ := leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [leftType] at payload
          exact False.elim (profile.left_valid payload invalid)
      | short childTrace circuit childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | value payload =>
          rw [leftType] at payload
          obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit evaluated
          exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related, successful bridge (outputType ▸ binary_result_typed functions profile resultRep) post.at_value.2⟩⟩
      | rightFault firstTrace continues secondTrace firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact profile.right_failure payload continues first second,
              .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, post.at_fault_type⟩⟩
      | value firstTrace continues secondTrace applied firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
            obtain ⟨sourceResult, result, actualApplied, resultRep, combined⟩ := profile.right_success leftPayload rightPayload continues first second applied
            have same := actualApplied.functional applied
            subst sourceResult
            exact ⟨.inRight .word result, finalStore, finalMap, finalWorld, by rw [Mode.binary_rename]; exact combined,
              .value (outputType ▸ resultRep), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, successful bridge (outputType ▸ binary_result_typed functions profile resultRep) post.at_value.2⟩⟩
      | panic firstTrace continues secondTrace panics firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
            exact ⟨_, finalStore, finalMap, finalWorld,
              by rw [Mode.binary_rename]; exact profile.right_panic leftPayload rightPayload continues first second panics,
              .fault (RecursiveStageMeaning.FaultTokens.panic _), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, panicked bridge post⟩⟩
      | invalid firstTrace continues secondTrace failed firstSmaller secondSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (Nat.lt_of_lt_of_le firstSmaller bounded) environments heaps locals agrees actualTyped initial admitted firstTrace
        cases represented with
        | @value _ coreValue payload =>
          rw [leftType] at payload
          obtain ⟨_, _, _, _, second, represented, _, maps, worlds, _⟩ :=
            rightIH _ (Nat.lt_of_lt_of_le secondSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 secondTrace
          rw [GenericExpressionMeaning.rename_prefix] at second
          cases represented with
          | value rightPayload =>
            rw [rightType] at rightPayload
            have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
            rcases profile.right_outcome leftPayload rightPayload continues first second with
              ⟨_, _, applied, _, _⟩ | ⟨_, panics, _⟩
            · exact False.elim (failed.excludes_application ⟨_, applied⟩)
            · exact False.elim (failed.excludes_panic panics)

    | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have conditionIH := fun n (bound : n < budget) => @meaning n bound _ _ _ conditionTree _ conditionFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) conditionFound)
      have thenIH := fun n (bound : n < budget) => @meaning n bound _ _ _ thenTree _ thenFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) thenFound)
      have elseIH := fun n (bound : n < budget) => @meaning n bound _ _ _ elseTree _ elseFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) elseFound)
      have sourceStep := CallableIndexedOwnedPreparedStagedOperatorSourceBounds.conditional_inv metadata form unique trace
      cases sourceStep with
      | fault childTrace childSmaller =>
        obtain ⟨_, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          conditionIH _ (Nat.lt_of_lt_of_le childSmaller bounded) environments heaps locals agrees actualTyped initial admitted childTrace
        cases represented with
        | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, by rw [choose_rename]; exact LocalControl.choose_failure type evaluated,
            .fault matched, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
      | @branch conditionSize branchSize flag middle outcome after conditionTrace branchTrace conditionSmaller branchSmaller =>
        obtain ⟨_, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          conditionIH _ (Nat.lt_of_lt_of_le conditionSmaller bounded) environments heaps locals agrees actualTyped initial admitted conditionTrace
        cases represented with
        | value payload =>
          obtain ⟨actualFlag, sourceEq, coreEq⟩ := bool_fields payload
          cases sourceEq
          subst coreEq
          cases flag with
          | false =>
            obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              elseIH _ (Nat.lt_of_lt_of_le branchSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
                (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 branchTrace
            rw [GenericExpressionMeaning.rename_prefix] at branch
            refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, by simpa only [elseType] using post⟩⟩
            · rw [choose_rename]; exact LocalControl.choose_false type first branch
            · simpa only [elseType] using represented
          | true =>
            obtain ⟨value, finalStore, finalMap, finalWorld, branch, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              thenIH _ (Nat.lt_of_lt_of_le branchSmaller bounded) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
                (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 branchTrace
            rw [GenericExpressionMeaning.rename_prefix] at branch
            refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
              firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, by simpa only [thenType] using post⟩⟩
            · rw [choose_rename]; exact LocalControl.choose_true type first branch
            · simpa only [thenType] using represented

  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ := raw
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩

/-- Completed native children produce their own staged grades and exact state. -/
theorem reflects_at [RecursiveStageMeaning.FaultTokens faults] (budget size : Nat) (bounded : size ≤ budget)
    (unique : NodeOccurrencesUnique invocation.source)
    (meaning : ReflectsBelow bridge context model stages invocation certificate faults budget) :
    ReflectsAt bridge context model stages invocation (Head compiled.compatible.checked invocation.source certificate) faults size := by
  intro scope id lowered tree root found sourceTyped mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees actualTyped initial admitted evaluated
  obtain ⟨originalTypes, operandTyped⟩ := operand_types unique found sourceTyped
  have raw : ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld root.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context root.type outcome reached := by
    cases tree with
    | @unary node operand childNode operator operandType resultType core childCode metadata form childFound inputType outputType profile child =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have ih := fun n (bound : n < budget) => @meaning n bound _ _ _ child _ childFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change operand ∈ [operand]; simp) childFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.unary operator operand) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [unary_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          ih _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_failure (operator := core) childEvaluation.sound) complete
          exact ⟨_, _, after, finalMap, finalWorld, .unaryOperandFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
      | caseRight childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          ih _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | value payload =>
          rw [inputType] at payload
          obtain ⟨sourceResult, result, applied, coreApplied, resultRep⟩ := profile.preserves payload
          obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic (LocalPrimitiveResults.unary_success childEvaluation.sound coreApplied) complete
          have childTrace := trace
          exact ⟨_, _, after, finalMap, finalWorld, .unary occurrence childTrace applied,
            .value (outputType ▸ resultRep), finalHeaps, maps, worlds, frame, heapMetadata, ⟨reached, related, successful bridge (outputType ▸ unary_result_typed functions profile resultRep) post.at_value.2⟩⟩
    | @binary node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile leftTree rightTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have leftIH := fun n (bound : n < budget) => @meaning n bound _ _ _ leftTree _ leftFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change left ∈ [left, right]; simp) leftFound)
      have rightIH := fun n (bound : n < budget) => @meaning n bound _ _ _ rightTree _ rightFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change right ∈ [left, right]; simp) rightFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.binary left operator right) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [Mode.binary_rename] at evaluated
      have complete := evaluated.sound
      rw [Mode.binary_eq] at evaluated
      cases evaluated with
      | caseLeft leftEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          leftIH _ (by omega) environments heaps locals agrees actualTyped initial admitted leftEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (mode.left_failure operator leftEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .binaryLeftFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
      | caseRight leftEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          leftIH _ (by omega) environments heaps locals agrees actualTyped initial admitted leftEvaluation
        cases represented with
        | @value sourceValue coreValue payload =>
          rw [leftType] at payload
          have firstTrace := trace
          rcases profile.left_progress payload with ⟨output, circuit⟩ | continues
          · obtain ⟨result, resultRep, combined⟩ := profile.short (right := rightCode.rename ξ) payload circuit leftEvaluation.sound
            obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
            exact ⟨_, _, middle, middleMap, middleWorld, .binaryShortCircuit occurrence firstTrace circuit,
              .value (outputType ▸ resultRep), middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, ⟨middleState, firstRelated, successful bridge (outputType ▸ binary_result_typed functions profile resultRep) firstPost.at_value.2⟩⟩
          · obtain ⟨rightSize, rightValue, rightStore, rightEvaluation, rightSmaller⟩ := RecursiveNamedExpressionSourceBounds.right_evaluated profile payload continues branch
            have shifted := rightEvaluation
            rw [← GenericExpressionMeaning.rename_prefix] at shifted
            obtain ⟨rightSourceSize, rightOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              rightIH rightSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees _)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 shifted
            cases represented with
            | fault matched =>
              have failed := trace
              have combined := profile.right_failure payload continues leftEvaluation.sound rightEvaluation.sound
              obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
              exact ⟨_, _, after, finalMap, finalWorld, .binaryRightFault occurrence firstTrace continues failed,
                .fault matched, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, post.at_fault_type⟩⟩
            | value rightPayload =>
              rw [rightType] at rightPayload
              have leftPayload := ValueRep.extend payload (.refl registry) maps worlds
              rcases profile.right_outcome leftPayload rightPayload continues leftEvaluation.sound rightEvaluation.sound with
                ⟨sourceResult, result, applied, resultRep, combined⟩ | ⟨_, panics, combined⟩
              · obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                have secondTrace := trace
                exact ⟨_, _, after, finalMap, finalWorld, .binary occurrence firstTrace continues secondTrace applied,
                  .value (outputType ▸ resultRep),   finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, successful bridge (outputType ▸ binary_result_typed functions profile resultRep) post.at_value.2⟩⟩
              · obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete combined
                have secondTrace := trace
                exact ⟨_, _, after, finalMap, finalWorld, .binaryPanic occurrence firstTrace continues secondTrace panics,
                  .fault (RecursiveStageMeaning.FaultTokens.panic _), finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
                  firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, panicked bridge post⟩⟩

    | @conditional node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have conditionIH := fun n (bound : n < budget) => @meaning n bound _ _ _ conditionTree _ conditionFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change condition ∈ [condition, thenId, elseId]; simp) conditionFound)
      have thenIH := fun n (bound : n < budget) => @meaning n bound _ _ _ thenTree _ thenFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change thenId ∈ [condition, thenId, elseId]; simp) thenFound)
      have elseIH := fun n (bound : n < budget) => @meaning n bound _ _ _ elseTree _ elseFound
        (CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operandTyped
          (by rw [form]; change elseId ∈ [condition, thenId, elseId]; simp) elseFound)
      have occurrence : Staging.Recursive.Occurrence invocation id (.conditional condition thenId elseId) :=
        ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      rw [choose_rename] at evaluated
      have complete := evaluated.sound
      cases evaluated with
      | caseLeft childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
          conditionIH _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | fault matched =>
          have failed := trace
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalControl.choose_failure type childEvaluation.sound)
          exact ⟨_, _, after, finalMap, finalWorld, .conditionalFault occurrence failed, .fault matched,
            finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post.at_fault_type⟩
      | caseRight childEvaluation branch =>
        obtain ⟨childSourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
          conditionIH _ (by omega) environments heaps locals agrees actualTyped initial admitted childEvaluation
        cases represented with
        | value payload =>
          obtain ⟨flag, sourceEq, coreEq⟩ := bool_fields payload
          subst sourceEq
          subst coreEq
          have conditionTrace := trace
          obtain ⟨selectedSize, selected, selectedSmaller⟩ := RecursiveNamedExpressionSourceBounds.choose_branch_evaluated branch
          cases flag with
          | false =>
            change EvaluationSize selectedSize _ _ ((elseCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              elseIH selectedSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool false))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 selected
            refine ⟨_, outcome, after, finalMap, finalWorld, .conditional occurrence conditionTrace branchTrace,
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, by simpa only [elseType] using post⟩⟩
            simpa only [elseType] using represented
          | true =>
            change EvaluationSize selectedSize _ _ ((thenCode.rename ξ).weakenAt 0) _ _ at selected
            rw [← GenericExpressionMeaning.rename_prefix] at selected
            obtain ⟨childSourceSize, outcome, after, finalMap, finalWorld, branchTrace, represented, finalHeaps, maps, worlds, frame, heapMetadata, reached, related, post⟩ :=
              thenIH selectedSize (by omega) (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
                (GenericExpressionMeaning.agree_prefix agrees (.bool true))
              (.cons .bool (actualTyped.weaken firstWorlds)) middleState firstPost.at_value.2 selected
            refine ⟨_, outcome, after, finalMap, finalWorld, .conditional occurrence conditionTrace branchTrace,
              ?_, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans heapMetadata, ⟨reached, callerProtocol.trans firstRelated related, by simpa only [thenType] using post⟩⟩
            simpa only [thenType] using represented

  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩ := raw
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationOperatorBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationBootstrapRootState
/-! The actual bootstrap constructs the owned state used by the public root.
The key is fixed before choosing a function model: initialized globals, no
capture prefix, and physical frame zero. Native completion fixes the complete
store, and store typing fixes the exact world. The original stored authority
supplies empty stable history, source heap representation and global reads. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationBootstrapRootState
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedHistory
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)

/-- The real initial frame is at zero; each global keeps its prepared slot. -/
def key (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Key compiled (Program.ofChecked compiled.sourceProgram) :=
  ⟨(fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot), 0, 0⟩

def keys (compiled : SourceCoreUnifiedCompilation.Compiled) :
    List (Key compiled (Program.ofChecked compiled.sourceProgram)) := [key compiled]

def owner (compiled : SourceCoreUnifiedCompilation.Compiled) : OwnedKey (keys compiled) :=
  ⟨⟨0, by simp [keys]⟩⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}

/-- The original entry constructor retains the empty histories omitted by the
older existential bootstrap packet. Its actual native typing fixes the world. -/
private theorem initial
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (ledger : RecursiveNamedCatalog.Ledger headers compiled.indexed.secondPass.closures)
    (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
    (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ caller : State headers (keys compiled)
        ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type,
          ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
          SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
        ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type) ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      (∀ header, header ∈ headers →
        (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
          some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
            ((owner compiled).key.locations header))) ∧
      (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨world, entry, heaps, receipt⟩ :=
    RecursiveNamedCatalogPreparedInitializationReceipts.entry_with_constructor
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) compiled headers
      ledger sizes locals accepted rfl functions registry
  have worldEq := heaps.runtime_hasTypes.world_eq
  subst world
  let row : CallableIndexedAuthorityPool.EntryValid
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) headers (key compiled) []
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type) ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled) := by
    refine { authority := entry.authority, frame_eq := ?_ }
    change entry.authority.frameLocation = 0
    exact receipt.frameLocation
  let caller : State headers (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩ :=
    CallableIndexedAuthorityPool.Pool.singleton row
  refine ⟨caller, ?_, heaps, ?_, ?_⟩
  · intro selected
    have same : selected = (owner compiled).position := by
      apply Fin.ext
      have bound := selected.isLt
      change selected.val < 1 at bound
      change selected.val = 0
      omega
    subst selected
    change ∃ metadata, Carries compiled.indexed.ancestry.graph.inputs
      compiled.indexed.ancestry.graph.table entry.authority.current entry.authority.ghost metadata
    rw [receipt.current, receipt.ghost]
    exact ⟨none, .empty⟩
  · intro header member
    have reference : (RecursiveNamedCatalogPreparedInitialization.environment compiled)[header.slot]? =
      some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
        (RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)) := by
      simpa only [List.length_nil, Nat.zero_add] using entry.globals header member
    rw [RecursiveNamedPublicBootstrapGlobals.environment_eq] at reference
    exact reference
  · intro context cell member
    exact nomatch member

/-- Accepted finite rows derive their ledger, global sizes and empty locals.
The actual completed bootstrap fixes the returned native store before the
owned state is constructed. No initial pool, stable-row or heap law is supplied. -/
theorem of_completed
    (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧
      finalStore = RecursiveNamedCatalogPreparedInitialization.store compiled ∧
      ∃ caller : State (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) (keys compiled)
          ⟨[], [], finalStore.map Value.type, ⟨[]⟩, finalStore,
            SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
        CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
        CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions []
          (finalStore.map Value.type) ⟨[]⟩ finalStore ∧
        (∀ header, header ∈ CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows →
          (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
            some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
              ((owner compiled).key.locations header))) ∧
        (∀ context, Dynamic.HeapWellTyped context ⟨[]⟩) := by
  obtain ⟨result, storeEq⟩ := RecursiveNamedCatalogPreparedInitialization.completed_store accepted completed
  refine ⟨result, storeEq, ?_⟩
  rw [storeEq]
  exact initial accepted
    (show RecursiveNamedCatalog.Ledger (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) compiled.indexed.secondPass.closures from
      ⟨by rw [CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.slots inputs rows]; exact distinct,
       bodyTyping.function_ids, CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.cache inputs rows⟩)
    (CallableIndexedOwnedPreparedFiniteNamedInventories.globals rows)
    (CallableIndexedOwnedPreparedFiniteNamedBootstrapReceipts.empty_locals inputs rows)
    functions registry

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationBootstrapRootState
end
