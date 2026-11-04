import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionMethods
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionExpressions
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.NamedCalls
import Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.GlobalInitialization
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinRuntime
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.ImperativeFor
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms

/-!
# Prepared methods

Selection and runtime meaning of prepared methods, catalog entries, body and hook meaning, and the runtime profile factory.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
/-! Actual operator selection retains the full synthetic method, ordered
source evidence, and the compiler's chosen plan row. It does not reinterpret
an implementation method as an ordinary program function. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
open Frontend SourceInference TypeSystem
open CallableCoercionMethodCertificates (Roots)
open CallableCoercionSourceSelection (MethodCertificate)
open CallableCoercionMethodInstantiation (Selection)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : action >>= next = .ok value) : ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem require_ok {α ε : Type} {condition : Prop} [Decidable condition]
    {action : Except ε α} {error : ε} {value : α}
    (accepted : (if condition then action else .error error) = .ok value) :
    condition ∧ action = .ok value := by
  split at accepted
  · exact ⟨‹condition›, accepted⟩
  · cases accepted

theorem unary_of_accepted {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {operator : Syntax.UnaryOp} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
    (accepted : SourceCompilationPlan.checkedUnaryOperatorMethod program caller node available operator = .ok selection) :
    ∃ traitName methodName methodIds,
      Detail.unaryOperatorDispatch operator = .traitMethod traitName methodName ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some (selection.primaryRequirement :: methodIds) ∧
      Nonempty (MethodCertificate program caller node available selection.primaryRequirement methodIds 1
        traitName methodName selection.method) := by
  simp only [SourceCompilationPlan.checkedUnaryOperatorMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i profile profileFound
  rcases profile with ⟨traitName, methodName⟩
  have dispatch : Detail.unaryOperatorDispatch operator = .traitMethod traitName methodName := by
    cases operator <;> cases profileFound <;> rfl
  split at accepted <;> try contradiction
  rename_i requirements ordinary
  cases requirements with
  | nil => cases accepted
  | cons primaryId methodIds =>
    dsimp only at accepted
    split at accepted <;> try contradiction
    obtain ⟨row, rowFound, accepted⟩ := bind_ok accepted
    obtain ⟨primary, primarySelected, accepted⟩ := bind_ok accepted
    split at accepted <;> try contradiction
    rename_i traitId goalTrait
    split at accepted <;> try contradiction
    rename_i trait found
    obtain ⟨traitNameEq, accepted⟩ := require_ok accepted
    obtain ⟨predicates, predicatesFound, accepted⟩ := bind_ok accepted
    obtain ⟨lengthEq, accepted⟩ := require_ok accepted
    obtain ⟨methodEvidence, methodsSelected, accepted⟩ := bind_ok accepted
    obtain ⟨method, methodChecked, accepted⟩ := bind_ok accepted
    have checked := mapError_ok methodChecked
    obtain ⟨inputTypes, accepted⟩ := require_ok accepted
    split at accepted <;> try contradiction
    obtain ⟨operand, operandFound, accepted⟩ := bind_ok accepted
    obtain ⟨operandType, accepted⟩ := require_ok accepted
    obtain ⟨resultType, accepted⟩ := require_ok accepted
    obtain ⟨rawType, accepted⟩ := require_ok accepted
    cases accepted
    let roots := Roots.of_selected primarySelected methodsSelected checked
    obtain ⟨selected⟩ := CallableCoercionMethodInstantiation.selection roots.checked
    have goalEq : selected.goal = row.predicate := by
      have matched := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ primarySelected
      change SourceCompilationPlan.runtimeEvidenceGoal roots.primary = row.predicate at matched
      rw [selected.primaryShape] at matched
      exact matched
    have traitIdEq : selected.trait.id = traitId := by
      have eq := selected.goalTrait
      rw [goalEq, goalTrait] at eq
      exact (ProgramTraitId.declaration.inj eq).symm
    have selectedLookup := selected.traitLookup
    have owner : selected.declaration.traitMethod.trait = selected.trait.id := by
      unfold ProgramSignatures.trait? at selectedLookup
      have eq := List.find?_some (p := fun trait : ProgramTraitSignature =>
        decide (trait.id = selected.declaration.traitMethod.trait)) selectedLookup
      exact (of_decide_eq_true eq).symm
    rw [owner, traitIdEq] at selectedLookup
    have same := Option.some.inj (selectedLookup.symm.trans found)
    exact ⟨traitName, methodName, methodIds, dispatch, ordinary,
      ⟨⟨roots, selected, by simpa only [same] using traitNameEq⟩⟩⟩

theorem binary_of_accepted {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
    {node : ExpressionNode} {available : SourceTypedRuntime.RuntimeEvidenceEnvironment}
    {operator : Syntax.BinaryOp} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}
    (accepted : SourceCompilationPlan.checkedBinaryOperatorMethod program caller node available operator = .ok selection) :
    ∃ traitName methodName methodIds,
      Detail.binaryOperatorDispatch operator = .traitMethod traitName methodName ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some (selection.primaryRequirement :: methodIds) ∧
      Nonempty (MethodCertificate program caller node available selection.primaryRequirement methodIds 1
        traitName methodName selection.method) := by
  simp only [SourceCompilationPlan.checkedBinaryOperatorMethod, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at accepted
  split at accepted <;> try contradiction
  rename_i profile profileFound
  rcases profile with ⟨traitName, methodName⟩
  have dispatch : Detail.binaryOperatorDispatch operator = .traitMethod traitName methodName := by
    cases operator <;> cases profileFound <;> rfl
  split at accepted <;> try contradiction
  rename_i requirements ordinary
  cases requirements with
  | nil => cases accepted
  | cons primaryId methodIds =>
    dsimp only at accepted
    split at accepted <;> try contradiction
    obtain ⟨row, rowFound, accepted⟩ := bind_ok accepted
    obtain ⟨primary, primarySelected, accepted⟩ := bind_ok accepted
    split at accepted <;> try contradiction
    rename_i traitId goalTrait
    split at accepted <;> try contradiction
    rename_i trait found
    obtain ⟨traitNameEq, accepted⟩ := require_ok accepted
    obtain ⟨predicates, predicatesFound, accepted⟩ := bind_ok accepted
    obtain ⟨lengthEq, accepted⟩ := require_ok accepted
    obtain ⟨methodEvidence, methodsSelected, accepted⟩ := bind_ok accepted
    obtain ⟨method, methodChecked, accepted⟩ := bind_ok accepted
    have checked := mapError_ok methodChecked
    obtain ⟨inputTypes, accepted⟩ := require_ok accepted
    split at accepted <;> try contradiction
    obtain ⟨left, leftFound, accepted⟩ := bind_ok accepted
    obtain ⟨right, rightFound, accepted⟩ := bind_ok accepted
    obtain ⟨operandType, accepted⟩ := require_ok accepted
    obtain ⟨resultType, accepted⟩ := require_ok accepted
    obtain ⟨rawType, accepted⟩ := require_ok accepted
    cases accepted
    let roots := Roots.of_selected primarySelected methodsSelected checked
    obtain ⟨selected⟩ := CallableCoercionMethodInstantiation.selection roots.checked
    have goalEq : selected.goal = row.predicate := by
      have matched := SourceCompilationPlan.exactRuntimeRequirementEvidence_success_goal _ _ _ _ _ _ _ primarySelected
      change SourceCompilationPlan.runtimeEvidenceGoal roots.primary = row.predicate at matched
      rw [selected.primaryShape] at matched
      exact matched
    have traitIdEq : selected.trait.id = traitId := by
      have eq := selected.goalTrait
      rw [goalEq, goalTrait] at eq
      exact (ProgramTraitId.declaration.inj eq).symm
    have selectedLookup := selected.traitLookup
    have owner : selected.declaration.traitMethod.trait = selected.trait.id := by
      unfold ProgramSignatures.trait? at selectedLookup
      have eq := List.find?_some (p := fun trait : ProgramTraitSignature =>
        decide (trait.id = selected.declaration.traitMethod.trait)) selectedLookup
      exact (of_decide_eq_true eq).symm
    rw [owner, traitIdEq] at selectedLookup
    have same := Option.some.inj (selectedLookup.symm.trans found)
    exact ⟨traitName, methodName, methodIds, dispatch, ordinary,
      ⟨⟨roots, selected, by simpa only [same] using traitNameEq⟩⟩⟩


open Core
open CallableCoercionExpressionCertificates (Lowered Projector Specialized NativeCall Output rawNode)

/-- The actual native signature check keeps the entire specialized carrier,
its raw function type, staging guard, and one physical global row. -/
structure Target (project : Projector) (compilation : SourceCoreFunctions.Context)
    (node : ExpressionNode) (key : SourceCompilationPlan.Key) (policy : SourceCoreFunctions.CallablePolicy)
    (signature : SourceCoreCalls.Signature) (index : Nat) where
  specialized : Specialized
  parameter : TypeSystem.Ty
  result : TypeSystem.Ty
  selected : SourceCompilationPlan.exactSpecialization compilation.plan key = .ok specialized
  staged : (!policy.allowStaged &&
    (specialized.function.returnComptime || specialized.function.typedBody.inputs.any (·.comptime))) = false
  functionType : specialized.function.type = .function parameter result
  global : compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key)) = [(signature, index)]
  parameterProjected : project (.occurrence node.id.occurrence) parameter = .ok signature.parameterType
  resultProjected : project (.occurrence node.id.occurrence) result = .ok signature.resultType

private theorem ensure_eq {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty} {returned : Unit}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok returned) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted <;> simp_all

/-- The premise is the compiler's private signature action by definitional
identity. No additional action or implementation-method checking is performed. -/
private theorem target_of_accepted {project : Projector} {compilation : SourceCoreFunctions.Context}
    {node : ExpressionNode} {key : SourceCompilationPlan.Key} {policy : SourceCoreFunctions.CallablePolicy}
    {signature : SourceCoreCalls.Signature} {index : Nat}
    (accepted : ((do
      let actual ← (SourceCompilationPlan.exactSpecialization compilation.plan key).mapError SourceCoreBasic.Error.callPreparation
      if !policy.allowStaged && (actual.function.returnComptime || actual.function.typedBody.inputs.any (·.comptime)) then
        throw (.unsupportedExpression node.id node.form)
      let (parameter, result) ← match actual.function.type with
        | .function parameter result => pure (parameter, result)
        | _ => throw (.callPreparation (.invalidFunctionType key actual.function.type))
      let (stored, index) ← match compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key)) with
        | [row] => pure row
        | [] => throw (.callPreparation (.missingSpecialization key))
        | rows => throw (.callPreparation (.duplicateSpecialization key rows.length))
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.parameterType (← project (.occurrence node.id.occurrence) parameter)
      SourceCoreBasic.ensureType (.occurrence node.id.occurrence) stored.resultType (← project (.occurrence node.id.occurrence) result)
      pure (index, stored)) : Except SourceCoreBasic.Error (Nat × SourceCoreCalls.Signature)) = .ok (index, signature)) :
    Nonempty (Target project compilation node key policy signature index) := by
  obtain ⟨actual, selected, accepted⟩ := bind_ok accepted
  by_cases staged : (!policy.allowStaged && (actual.function.returnComptime || actual.function.typedBody.inputs.any (·.comptime))) = true
  · simp [staged, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  · simp only [staged] at accepted
    cases functionType : actual.function.type <;>
      simp only [functionType, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted <;>
      try contradiction
    rename_i parameter result
    generalize global : compilation.globals.zipIdx.filter (fun row => decide (row.1.key = key)) = rows at accepted
    cases rows with
    | nil => cases accepted
    | cons row rows =>
      cases rows with
      | cons second rest => cases accepted
      | nil =>
        rcases row with ⟨stored, physical⟩
        obtain ⟨parameterType, projectedParameter, accepted⟩ := bind_ok accepted
        obtain ⟨_, parameterEq, accepted⟩ := bind_ok accepted
        obtain ⟨resultType, projectedResult, accepted⟩ := bind_ok accepted
        obtain ⟨_, resultEq, accepted⟩ := bind_ok accepted
        cases accepted
        exact ⟨⟨actual, parameter, result, mapError_ok selected, by simpa using staged,
          functionType, global, by rwa [← ensure_eq parameterEq] at projectedParameter,
          by rwa [← ensure_eq resultEq] at projectedResult⟩⟩

/-- The method call is selected at the original operator occurrence. Its
children and suffix keep the compiler's exact order, code and fuel. -/
structure Operator (program : CheckedProgram) (project : Projector) (caller : Specialized)
    (compilation : SourceCoreFunctions.Context) (child : SourceCoreEvidence.Child) (fuel : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (reasonAt : ExpressionId → Word) (policy : SourceCoreFunctions.CallablePolicy)
    (node : ExpressionNode) (output : Lowered)
    extends Output program project caller compilation child fuel source scope id reasonAt policy node output where
  requirements : List RequirementId
  ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements
  nonempty : requirements ≠ []
  selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod
  selectedMethod : (match node.form with
    | .unary operator _ => SourceCompilationPlan.checkedUnaryOperatorMethod program caller (rawNode node requirements) available operator
    | .binary _ operator _ => SourceCompilationPlan.checkedBinaryOperatorMethod program caller (rawNode node requirements) available operator
    | _ => .error (.unsupportedRequirements requirements)) = .ok selection
  dictionary : SourceTypedRuntime.RuntimeEvidenceEnvironment
  materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller (rawNode node requirements) selection = .ok dictionary
  key : SourceCompilationPlan.Key
  edge : SourceCompilationPlan.exactCallKey compilation.plan compilation.owner id selection.method.specialized.key = .ok key
  arguments : List ExpressionId
  form : (∃ operator operand, node.form = .unary operator operand ∧ arguments = [operand]) ∨
    (∃ operator left right, node.form = .binary left operator right ∧ arguments = [left, right])
  loweredArguments : List Lowered
  argumentsAccepted : arguments.mapM (fun argument => child fuel source scope argument reasonAt) = .ok loweredArguments
  native : NativeCall compilation scope key (SourceCoreCalls.packArguments loweredArguments) operand
  target : Target project compilation (rawNode node requirements) key policy native.signature native.index


theorem of_accepted {program : CheckedProgram} {project : Projector} {caller : Specialized}
    {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
    {node : ExpressionNode} {output : Lowered} {requirements : List RequirementId}
    (found : source.lookupExpression? id = some node)
    (form : (∃ operator operand, node.form = .unary operator operand) ∨
      (∃ operator left right, node.form = .binary left operator right))
    (ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? node = some requirements)
    (nonempty : requirements ≠ [])
    (original : SourceCoreEvidence.lowerWithProjector program project caller compilation child fuel source scope id reasonAt policy = .ok (some output)) :
    Nonempty (Operator program project caller compilation child fuel source scope id reasonAt policy node output) := by
  have notEmpty : requirements.isEmpty = false := by cases requirements <;> simp_all
  have accepted := original
  rcases form with ⟨operator, operandId, form⟩ | ⟨operator, leftId, rightId, form⟩
  all_goals
    simp only [SourceCoreEvidence.lowerWithProjector, found, form, ordinary,
      Bool.not_false, Bool.and_true, Bool.or_false, Bool.and_false,
      bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
    split at accepted <;> try { cases accepted }
    split at accepted <;> try { cases accepted }
    rename_i pathValid
    split at accepted <;> try { cases accepted }
    rename_i ownerNe
    have owner : caller.key = compilation.owner := Classical.not_not.mp ownerNe
    obtain ⟨available, resolved, accepted⟩ := bind_ok accepted
    simp only [notEmpty, Bool.false_eq_true, if_false] at accepted
    obtain ⟨selection, methodAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨returned, discarded, accepted⟩ := bind_ok accepted
    have materialization : ∃ dictionary,
        SourceCompilationPlan.operatorMethodRuntimeEvidence program caller (rawNode node requirements) selection = .ok dictionary := by
      have normalized : (discard ((SourceCompilationPlan.operatorMethodRuntimeEvidence program caller
          (rawNode node requirements) selection).mapError SourceCoreBasic.Error.callPreparation) : Except SourceCoreBasic.Error Unit) = .ok returned := by
        simpa only [rawNode, form] using discarded
      cases run : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller (rawNode node requirements) selection with
      | error error => simp only [run, Except.mapError, discard] at normalized; cases normalized
      | ok dictionary => exact ⟨dictionary, rfl⟩
    obtain ⟨dictionary, materialized⟩ := materialization
    obtain ⟨key, edgeAccepted, accepted⟩ := bind_ok accepted
    have edge : SourceCompilationPlan.exactCallKey compilation.plan compilation.owner id selection.method.specialized.key = .ok key := by
      have same := (lookupExpression?_sound found).2
      exact same ▸ mapError_ok edgeAccepted
    first
    | (obtain ⟨lowered, loweredAccepted, remaining⟩ := bind_ok accepted
       clear accepted
       let arguments : List ExpressionId := [operandId]
       let codes : List Lowered := [lowered]
       have argumentsAccepted : arguments.mapM (fun argument => child fuel source scope argument reasonAt) = .ok codes := by
         simp only [arguments, codes, List.mapM_cons, List.mapM_nil, loweredAccepted, bind, Except.bind, pure, Except.pure]
       have argsForm : (∃ operator operand, node.form = .unary operator operand ∧ arguments = [operand]) ∨
           (∃ operator left right, node.form = .binary left operator right ∧ arguments = [left, right]) :=
         .inl ⟨operator, operandId, form, rfl⟩)
    | (obtain ⟨codes, argumentsAccepted, remaining⟩ := bind_ok accepted
       clear accepted
       let arguments : List ExpressionId := [leftId, rightId]
       have argsForm : (∃ operator operand, node.form = .unary operator operand ∧ arguments = [operand]) ∨
           (∃ operator left right, node.form = .binary left operator right ∧ arguments = [left, right]) :=
         .inr ⟨operator, leftId, rightId, form, rfl⟩)
    obtain ⟨operand, invoked, remaining⟩ := bind_ok remaining
    obtain ⟨inputType, inputProjected, remaining⟩ := bind_ok remaining
    obtain ⟨_, inputEq, remaining⟩ := bind_ok remaining
    obtain ⟨result, suffix, remaining⟩ := bind_ok remaining
    obtain ⟨outputType, outputProjected, remaining⟩ := bind_ok remaining
    obtain ⟨_, outputEq, remaining⟩ := bind_ok remaining
    cases remaining
    obtain ⟨pair, signatureAccepted, invoked⟩ := bind_ok invoked
    rcases pair with ⟨index, signature⟩
    obtain ⟨_, argumentType, emitted⟩ := bind_ok invoked
    have emittedEq : operand = ⟨signature.resultType, SourceCoreCalls.call signature
        (scope.length + compilation.administrativePrefix + index)
        (SourceCoreCalls.packArguments codes).expression compilation.internalReason⟩ := by
      exact (Except.ok.inj emitted).symm
    have targetExists : Nonempty (Target project compilation (rawNode node requirements) key policy signature index) := by
      apply target_of_accepted
      simp only [rawNode, form]
      exact signatureAccepted
    obtain ⟨target⟩ := targetExists
    refine ⟨{
      available := available, operand := operand, found := found, accepted := original,
      pathValid := pathValid, owner := owner, resolved := mapError_ok resolved,
      suffix := ⟨?_, suffix, ?_⟩,
      requirements := requirements, ordinary := ordinary, nonempty := nonempty,
      selection := selection, selectedMethod := ?_, dictionary := dictionary, materialized := materialized,
      key := key, edge := edge, arguments := arguments, form := argsForm,
      loweredArguments := codes, argumentsAccepted := argumentsAccepted,
      native := ⟨signature, index, target.global, ensure_eq argumentType, emittedEq⟩,
      target := target }⟩
    · change project (.occurrence node.id.occurrence) node.rawType = .ok inputType at inputProjected
      rwa [ensure_eq inputEq] at inputProjected
    · change project (.occurrence node.id.occurrence) node.type = .ok outputType at outputProjected
      rwa [ensure_eq outputEq] at outputProjected
    · simpa only [form, rawNode] using mapError_ok methodAccepted


variable {program : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}

/-- One source receipt for the same actual operator selector. Requirement
positions and all returned implementation metadata are retained verbatim. -/
structure SourceReceipt
    (receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output) where
  traitName : String
  methodName : String
  methodIds : List RequirementId
  traitArity : Nat
  requirements : receipt.requirements = receipt.selection.primaryRequirement :: methodIds
  certificate : MethodCertificate program caller (rawNode node receipt.requirements)
    receipt.available receipt.selection.primaryRequirement methodIds traitArity traitName methodName receipt.selection.method

/-- The static method checker is inverted once at the actual unary or binary
site. No method body is rechecked and no ordinary function is fabricated. -/
theorem Operator.source_receipt
    (receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output) :
    Nonempty (SourceReceipt receipt) := by
  have accepted := receipt.selectedMethod
  have rawRequirements : SourceCompilationPlan.ordinaryOwnedRequirements? (rawNode node receipt.requirements) =
      some receipt.requirements := by
    change (if receipt.requirements.length < 0 then none else
      if receipt.requirements = receipt.requirements.take (receipt.requirements.length - 0) ++ [] then
        some (receipt.requirements.take (receipt.requirements.length - 0)) else none) = some receipt.requirements
    simp
  rcases receipt.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
  · simp only [form] at accepted
    obtain ⟨traitName, methodName, methodIds, _, owned, ⟨certificate⟩⟩ := unary_of_accepted accepted
    exact ⟨⟨traitName, methodName, methodIds, 1,
      Option.some.inj (rawRequirements.symm.trans owned), certificate⟩⟩
  · simp only [form] at accepted
    obtain ⟨traitName, methodName, methodIds, _, owned, ⟨certificate⟩⟩ := binary_of_accepted accepted
    exact ⟨⟨traitName, methodName, methodIds, 1,
      Option.some.inj (rawRequirements.symm.trans owned), certificate⟩⟩

open CallableNamedMetadata (environment)
open CallableCoercionMethodInstantiation (bodyInstance Formation)

/-- The actual authenticated dictionaries supply the independent source method
judgment. Caller-covered headers and full substitution formation remain explicit. -/
theorem SourceReceipt.selects
    (loadedAccepted : CallableMethodBodyCoherence.Checked program)
    {receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output}
    (selected : SourceReceipt receipt)
    (formed : Formation selected.certificate.selected.implementation selected.certificate.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) receipt.selection.method.specialized.parameterSubstitution)
    {context : Context} (signatures : context.signatures = program.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller receipt.selection.method) :
    Dynamic.OperatorMethodSelected (Program.ofChecked program) context (environment receipt.available)
      selected.traitName selected.methodName receipt.requirements
      (bodyInstance program receipt.selection.method) (environment receipt.dictionary) := by
  rw [selected.requirements]
  exact selected.certificate.selects loadedAccepted formed range signatures ledger assumptions
    receipt.resolved covered receipt.materialized

/-- Whole-program source validity supplies the existing method body typing
certificate. The complete scoped ledger and the actual method dictionary give
runtime validity at its exact monomorphic parameter context. -/
theorem selected_typed {sourceProgram : Program} {context : Context}
    {callerEvidence dictionary : Dynamic.EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : Dynamic.BodyInstance}
    (selected : Dynamic.OperatorMethodSelected sourceProgram context callerEvidence traitName methodName
      requirements body dictionary)
    (programTyped : ProgramWellFormed sourceProgram) :
    ∃ types lexicalContext facts,
      Dynamic.BodyInstanceTypingCertificate sourceProgram body types lexicalContext facts ∧
      CompatibleRuntimeContextValidity.Valid body.context.solvedRequirements lexicalContext dictionary := by
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ instantiated _ covers =>
    obtain ⟨types, lexicalContext, facts, typed⟩ := instantiated.certificate programTyped
    refine ⟨types, lexicalContext, facts, typed.toBodyInstanceTypingCertificate, ?_⟩
    exact (show CompatibleRuntimeContextValidity.Valid body.context.solvedRequirements body.context dictionary from
      ⟨rfl, typed.requirement_ledger.toRuntime, covers⟩).mono typed.typing.inputs_extend


/-- The retained checker record is the source of the full body, substitution,
unused ledger rows and original staging metadata. -/
theorem SourceReceipt.retained     (loadedAccepted : CallableMethodBodyCoherence.Checked program)
    {receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output}
    (selected : SourceReceipt receipt) :
    Nonempty (CallableCoercionBodyProvenance.Certificate program receipt.selection.method) := by
  obtain ⟨retained, member, sameId, sameChecked⟩ := selected.certificate.selected.toSelection.retained loadedAccepted
  exact ⟨⟨selected.certificate.selected.toSelection, retained, member, sameId, sameChecked⟩⟩

/-- Actual cached method rows retain the compiler's complete carrier, physical
position, generated roots and closure code. This receipt has no body meaning. -/
structure Cached (compiled : SourceCoreUnifiedCompilation.Compiled) (row : Specialized) where
  index : Nat
  named : SourceCoreGeneralFunctions.Function
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  code : Core.Expr
  selected : compiled.indexed.base.functions[index]? = some named
  same : named.specialized = row
  cached : compiled.indexed.secondPass.closures[index]? = some code
  compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics code

private theorem mapM_member {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} {input : α}
    (accepted : inputs.mapM action = .ok outputs) (member : input ∈ inputs) :
    ∃ output ∈ outputs, action input = .ok output := by
  induction inputs generalizing outputs with
  | nil => cases member
  | cons head tail ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, generated, accepted⟩ := bind_ok accepted
    obtain ⟨rest, remaining, accepted⟩ := bind_ok accepted
    cases accepted
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨first, by simp, generated⟩
    · obtain ⟨output, outputMember, generated⟩ := ih remaining member
      exact ⟨output, by simp [outputMember], generated⟩

/-- Final-plan membership includes appended implementation methods. The actual
reverse preparation pass supplies their cached positions without changing rows. -/
theorem cached_row (compiled : SourceCoreUnifiedCompilation.Compiled) {row : Specialized}
    (member : row ∈ compiled.indexed.base.plan.specializations) : Nonempty (Cached compiled row) := by
  have generated := RecursiveNamedPreparedParameterProjections.automatic_functions compiled.compatiblePrepared
  rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared] at member
  obtain ⟨named, namedMember, accepted⟩ := mapM_member generated (List.mem_reverse.mpr member)
  obtain ⟨index, selected⟩ := List.mem_iff_getElem?.mp namedMember
  have selected : compiled.indexed.base.functions[index]? = some named := by
    rwa [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared]
  obtain ⟨diagnostics, code, cached, ⟨compilation⟩⟩ := CallableIndexedNamedGeneration.compiled_at compiled.indexed selected
  exact ⟨⟨index, named, diagnostics, code, selected,
    (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1, cached, compilation⟩⟩

/-- Source method selection and actual cached compilation share one full method
body. The common frame constructor supplies its ordered roots and dictionary. -/
theorem Cached.frame {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod} (cached : Cached compiled method.specialized)
    {context : Context} {callerEvidence dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      traitName methodName requirements (bodyInstance compiled.sourceProgram method) dictionary) :
    CallableCoercionMethodFrame.Frame (bodyInstance compiled.sourceProgram method)
      (CallableCoercionMethodFrame.view (bodyInstance compiled.sourceProgram method) dictionary cached.compilation.statements) := by
  apply CallableCoercionMethodFrame.of_selected selected cached.compilation
  simp only [CallableIndexedNamedGeneration.source, cached.same, bodyInstance]

/-- The actual preparation scan and emitter select one complete method. The
returned visit retains its original worklist extension and staged boundary,
with the same ordered arguments and complete materialized dictionary. -/
theorem Operator.prepared
    (receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output)
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes) :
    ∃ visit : CallableCoercionPreparationSteps.OperatorVisit program caller receipt.available node compilation.plan,
      visit.requirements = receipt.requirements ∧ visit.selection = receipt.selection ∧
      visit.arguments = receipt.arguments ∧ visit.dictionary = receipt.dictionary ∧
      receipt.target.specialized = receipt.selection.method.specialized := by
  have operatorForm : CallableCoercionPreparationSteps.OperatorForm node := by
    rcases receipt.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩ <;>
      simp only [CallableCoercionPreparationSteps.OperatorForm, form]
  obtain ⟨visit⟩ := CallableCoercionPreparation.operator_visit prepared callerMember nodeMember
    operatorForm receipt.ordinary receipt.nonempty receipt.resolved
  have requirements := Option.some.inj (visit.owned.symm.trans receipt.ordinary)
  have selected := visit.selected
  rw [requirements] at selected
  have selection : visit.selection = receipt.selection :=
    Except.ok.inj (selected.symm.trans receipt.selectedMethod)
  have materialized := visit.materialized
  rw [requirements, selection] at materialized
  have dictionary : visit.dictionary = receipt.dictionary :=
    Except.ok.inj (materialized.symm.trans receipt.materialized)
  have arguments : visit.arguments = receipt.arguments := by
    have selected := visit.argumentsSelected
    rcases receipt.form with ⟨operator, operand, form, actual⟩ | ⟨operator, left, right, form, actual⟩ <;>
      simpa only [CallableCoercionPreparationSteps.operatorOwnedNode, form, pure, Except.pure,
        Except.ok.injEq, actual] using selected.symm
  have retained := visit.finalSelected
  rw [selection] at retained
  have emitted := (congrArg (SourceCompilationPlan.exactSpecialization compilation.plan)
    (CallableCoercionPreparation.exact_call_key receipt.edge)).symm.trans receipt.target.selected
  exact ⟨visit, requirements, selection, arguments, dictionary,
    Except.ok.inj (emitted.symm.trans retained)⟩

private theorem exact_member {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {row : Specialized} (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact (List.mem_filter.mp member).1

/-- The emitted target comes from the actual final plan. Its cached row and
closure therefore carry the selected method's entire retained record. -/
theorem Operator.cached
    (receipt : Operator program project caller compilation child fuel source scope id reasonAt policy node output)
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget program before preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (compiled : SourceCoreUnifiedCompilation.Compiled)
    (samePlan : compilation.plan = compiled.indexed.base.plan) :
    Nonempty (Cached compiled receipt.selection.method.specialized) := by
  obtain ⟨_, _, _, _, _, same⟩ := receipt.prepared prepared callerMember nodeMember
  have selected := receipt.target.selected
  rw [same, samePlan] at selected
  exact cached_row compiled (exact_member selected)

/-- Preparation, actual lowering and independent source selection meet at the
same cached implementation method. All source formation and caller evidence
conditions stay explicit; the result asserts only the static body frame. -/
theorem SourceReceipt.prepared_frame {compiled : SourceCoreUnifiedCompilation.Compiled}
    {receipt : Operator compiled.sourceProgram project caller compilation child fuel source scope id reasonAt policy node output}
    (selected : SourceReceipt receipt)
    {before : SourceCompilationPlan.Plan} {preparationFuel budget : Nat}
    (prepared : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget compiled.sourceProgram before
      preparationFuel budget = .ok compilation.plan)
    (callerMember : caller ∈ compilation.plan.specializations)
    (nodeMember : .expression node ∈ caller.function.typedBody.nodes)
    (samePlan : compilation.plan = compiled.indexed.base.plan)
    (loadedAccepted : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (formed : Formation selected.certificate.selected.implementation selected.certificate.selected.declaration)
    (range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) receipt.selection.method.specialized.parameterSubstitution)
    {context : Context} (signatures : context.signatures = compiled.sourceProgram.signatures)
    (ledger : context.solvedRequirements = caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ caller.assumptions → goal ∈ context.assumptions)
    (covered : CallableCoercionEvidenceOrigins.CallerCovered caller receipt.selection.method) :
    ∃ cached : Cached compiled receipt.selection.method.specialized,
      CallableCoercionMethodFrame.Frame (bodyInstance compiled.sourceProgram receipt.selection.method)
        (CallableCoercionMethodFrame.view (bodyInstance compiled.sourceProgram receipt.selection.method)
          (environment receipt.dictionary) cached.compilation.statements) := by
  obtain ⟨cached⟩ := receipt.cached prepared callerMember nodeMember compiled samePlan
  exact ⟨cached, cached.frame (selected.selects loadedAccepted formed range signatures ledger assumptions covered)⟩

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSelection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
/-! Actual prepared methods retain their independent trait-method source frame,
full dictionary and installed code. The body profile is static and uses reached
builtin runtime certificates, including the complete unused requirement ledger.
Original native prefix witnesses supply every finite body bound. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames

/-- The actual measured marked prefix, with no unsized-to-sized recovery. -/
structure Prefix (layout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : SourceCoreCallableIndexedFrames.Frame) (values : SourceCoreCompatibleValues.Context)
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (function : Dynamic.Closure) (context : SourceSemantics.Context) (bindings : List Binding)
    (arguments : List Dynamic.Value) (before : Dynamic.Heap) (initialStore : Store)
    (initialMap : LocationMap) (initialWorld : StoreTyping) (administrative actualContext : Core.Context)
    (actual : Environment) (ξ : Renaming) (parameterCode body : Expr) (size : Nat) (result : Value) (afterStore : Store) where
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actualBody : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate [] before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative)
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical ambient.definitions
  heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actualBody
  actualTyped : RuntimeEnvironmentHasTypes world actualBody
    (CallableIndexedParameterTyped.prefixContext bindings actualContext) ambient.definitions
  reference : canonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
    some (.cellRef layout.type contextLocation)
  read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native)
  unmapped : contextLocation ∉ mapping
  childSize : Nat
  completed : EvaluationSize childSize actualBody store (body.rename embedding) result afterStore
  bounded : childSize ≤ size
  strict : bindings ≠ [] → childSize < size

private theorem insert_at_suffix (added suffix : Environment) (value : Value) :
    Environment.insertAt (added ++ suffix) added.length value = added ++ value :: suffix := by
  induction added with
  | nil => simp [Environment.insertAt]
  | cons head tail ih => simpa [Environment.insertAt] using congrArg (List.cons head) ih

private theorem insert_administrative {catalog : SourceCoreDataCatalog.Catalog} {definitions : DataEnvironment}
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {environment : Dynamic.Environment} {canonical : Environment}
    (related : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    {value : Value} {type : Ty} (typed : RuntimeValueHasType world value type definitions) :
    DataHeap.EnvRepresents catalog mapping world (type :: administrative) scope environment
      (Environment.insertAt canonical scope.length value) definitions := by
  induction related with
  | nil values => exact .nil (by simpa [Environment.insertAt] using RuntimeEnvironmentHasTypes.cons typed values)
  | cons reference _ ih => exact .cons reference ih
  | internal reference absent _ ih => exact .internal reference absent ih


theorem parameter_prefix_with_spine
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (parameterCode.rename ξ) result afterStore) :
    ∃ entry : Prefix layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body size result afterStore,
      ∃ added : Environment, added.length = bindings.length ∧
        entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical := by
  have tree := CallableIndexedParameterCertificates.of_accepted onError accepted
  have sourceLayout : EnvironmentsAgree (Renaming.insertion 0) canonical
      (DataPatternValues.packValues nativeArguments :: canonical) := by
    intro index value found; exact found
  have length : (bindings.map Prod.snd).length = nativeArguments.length := by simpa using represented.length.2
  obtain ⟨environment, heap, finalCanonical, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding, child,
      allocated, finalEnvironments, finalHeaps, maps, worlds, preservation, _, lookups, spine, finalTyped, bodyCompletion, childLe, childStrict⟩ :=
    RecursiveNamedCallBounds.parameter_prefix tree definitions registered represented environments heaps
      sourceLayout actualLayout actualTyped (allTypes := bindings.map Prod.snd) (named := true) rfl (by simp) length
      (fun {_ _} found => by simpa using found) (CallableIndexedParameters.inputKinds inputs)
      (by simpa using reference) read unmapped completed
  obtain ⟨added, prefixLength, canonicalEq, logicalEq⟩ := spine
  have bundleTyped := (CallableIndexedParameters.Arguments.pack_typed represented).weaken worlds
  have finalWithBundle := insert_administrative finalEnvironments bundleTyped
  have scopeLength : (bindings.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) []).length = bindings.length := by simp
  have exactEnvironment : Environment.insertAt finalCanonical bindings.length
      (DataPatternValues.packValues nativeArguments) = finalLogical := by
    rw [canonicalEq, ← prefixLength, insert_at_suffix, logicalEq]
  rw [scopeLength, exactEnvironment, CallableIndexedParameters.scope_eq] at finalWithBundle
  have finalReference : finalLogical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + globals]? =
      some (.cellRef layout.type contextLocation) := by
    rw [logicalEq]
    simp only [List.length_map, List.length_reverse]
    have index : bindings.length + 1 + globals = added.length + (globals + 1) := by omega
    rw [index, List.getElem?_append_right (by omega)]
    simpa using reference
  obtain ⟨finalUnmapped, unchanged⟩ := preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1
  rw [← parameters] at allocated
  have mono := FunctionCallBody.mono_binders extended
  refine ⟨⟨environment, heap, finalLogical, finalActual, finalStore, finalMap, finalWorld, embedding,
    allocated, by simpa using finalWithBundle, finalHeaps,
    GenericLexicalContext.binders_agree mono.1 mono.2 initialLocals allocated,
    maps, worlds, preservation, GenericLexicalContext.binders_metadata allocated, lookups, finalTyped,
    finalReference, unchanged.trans read, finalUnmapped, child, bodyCompletion, childLe, childStrict⟩, added, prefixLength, ?_⟩
  exact logicalEq

theorem parameter_prefix
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {bindings : List Binding} {output : Ty} {body parameterCode : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      function.source [] bindings output SourceCoreFunctions.argumentProjection body = .ok parameterCode)
    (parameters : function.parameters = bindings.map Prod.fst)
    (inputs : function.source.inputs = bindings.map Prod.fst)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (definitions : layouts.definitions = ambient.definitions) (registered : layout.Registered ambient.definitions)
    {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world bindings arguments nativeArguments)
    {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
    {ξ : Renaming} {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      administrative [] [] canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode layout native))
    (unmapped : contextLocation ∉ mapping)
    {size : Nat} {result : Value} {afterStore : Store}
    (completed : EvaluationSize size actual store (parameterCode.rename ξ) result afterStore) :
    Nonempty (Prefix layout globals contextLocation native values functions registry function context bindings arguments before store mapping world
      administrative actualContext actual ξ parameterCode body size result afterStore) := by
  obtain ⟨entry, _⟩ := parameter_prefix_with_spine functions onError accepted parameters inputs extended definitions registered
    represented environments heaps initialLocals actualLayout actualTyped reference read unmapped completed
  exact ⟨entry⟩

section ConcreteBody
structure Body (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frameLayout : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : SourceCoreCompatibleValues.Context) (function : Dynamic.Closure)
    (expressionSyntax : ExpressionId → Prop) (readFuel : Nat) (solved : List SolvedRequirement)
    (reasonAt : ExpressionId → Word) (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (administrative : Core.Context) (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (output : Ty) (code : Expr) (fellThrough escaped : Word)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  flow : Expr
  tree : GenericImperativeMatch.Tree layouts owner active frameLayout globals onError values function.source
    expressionSyntax (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values
      function.source context solved reasonAt) ambient.definitions administrative context scope
    (.statements true function.body) function.resultType output flow
  sites : tree.CatalogSites .reachable registry faults
  valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence
  projection : values.checked.catalog.project function.resultType = .ok output
  unique : NodeOccurrencesUnique function.source
  emitted : code = CompatibleStatements.finish output flow fellThrough escaped

private abbrev builtinEntry : ProtectedExpressionMeaning.Entry := fun _ _ _ _ _ _ => True
private theorem builtinTransport : ProtectedExpressionMeaning.Transport builtinEntry := ⟨fun _ _ _ _ _ => True.intro⟩
private theorem builtinBindings : ProtectedExpressionMeaning.Binds builtinEntry :=
  ⟨fun _ => True.intro, fun _ => True.intro⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {expressionSyntax : ExpressionId → Prop} {readFuel : Nat} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {output : Ty} {code : Expr} {fellThrough escaped : Word}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (body : Body layouts owner active frameLayout globals onError values function expressionSyntax readFuel solved reasonAt
    ambient administrative context scope output code fellThrough escaped registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (escapedFault : faults .controlEscapedFunction escaped)

/-- A covering dictionary changes only the source evidence field. The actual
flow, tree, sites, and complete runtime ledger are retained verbatim. -/
def Body.with_evidence (dictionary : Dynamic.EvidenceEnvironment) (covers : dictionary.Covers context) :
    Body layouts owner active frameLayout globals onError values { function with evidence := dictionary }
      expressionSyntax readFuel solved reasonAt ambient administrative context scope output code
      fellThrough escaped registry faults :=
  { flow := body.flow, tree := body.tree, sites := body.sites
    valid := ⟨body.valid.ledger, body.valid.runtime, covers⟩
    projection := body.projection, unique := body.unique, emitted := body.emitted }

/-- The concrete builtin receipt keeps its original record type. Only its
static fields are passed to the shared body kernel. -/
def Body.toKernel : CallableRuntimeBodyKernel.BodyFor layouts owner active frameLayout globals onError values function
    expressionSyntax (fun context => CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt)
    (fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence) .reachable
    ambient administrative context scope output code fellThrough escaped registry faults :=
  { flow := body.flow, tree := body.tree, sites := body.sites, initialValid := body.valid
    projection := body.projection, unique := body.unique, emitted := body.emitted }

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault in
/-- The original source grade feeds the single imperative proof. The returned
heap and reached lexical exit belong to this exact emitted body. -/
theorem Body.preserves_sized (size : Nat)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid solved context function.evidence →
      RecursiveNamedHeaderContracts.AtMost size (fun child => RecursiveNamedBoundedContracts.PreservesAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt)
        faults builtinEntry) := by
    intro context valid child _
    exact RecursiveNamedBoundedContracts.preserves_at_of_unbounded
      (ProtectedExpressionMeaning.preserves_of_typed builtinEntry
        (CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime body.unique uninitialized missing)) child
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ :=
    body.toKernel.preserves_sized functions definitions registered extension program faithful observations escapedFault
      builtinTransport builtinBindings (fun valid extended => valid.extend extended) (fun valid => valid)
      size size (Nat.le_refl size) expressions environments heaps locals agrees typed reference read unmapped True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩


include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault in
/-- Source-only sizing is confined to preservation. -/
theorem Body.preserves
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.BodyTrace.has_size trace
  exact body.preserves_sized functions definitions registered extension program faithful observations functionTypes
    uninitialized missing escapedFault size environments heaps locals agrees typed reference read unmapped sized

include body definitions registered extension faithful observations functionTypes uninitialized missing escapedFault in
/-- Reflection consumes the actual measured body completion. The finish proof
passes its original strict flow child to the same bounded statement proof. -/
theorem Body.reflects_sized (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome := by
  have expressions : ∀ context, CompatibleRuntimeContextValidity.Valid solved context function.evidence →
      RecursiveNamedBoundedContracts.Below budget (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence
        function.source (CompatibleExpressionBuiltinRuntime.Certificate readFuel values function.source context solved reasonAt)
        faults builtinEntry) := by
    intro context valid
    exact RecursiveNamedBoundedContracts.reflects_below_of_unbounded
      (ProtectedExpressionMeaning.reflects_of_typed builtinEntry
        (CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
          program function.evidence valid.ledger valid.runtime uninitialized missing)) budget
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ :=
    body.toKernel.reflects_sized functions definitions registered extension program faithful observations functionTypes escapedFault
      builtinTransport builtinBindings (fun valid extended => valid.extend extended) (fun valid => valid)
      budget size within expressions environments heaps locals agrees typed reference read unmapped True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩


end ConcreteBody

section Hook
open CallableAncestryPairedLookup
open NamedCalls (withFrame_rename)
private theorem agree_prefix {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (saved : Value) :
    EnvironmentsAgree (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
      canonical (.unit :: saved :: actual) :=
  GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees saved) .unit

private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (layout : Layout) (index : Int) (environment : Environment)
    (store : Store) (saved : Value) :
    Evaluates (saved :: environment) store
      ((SourceCoreCallableIndexedDispatch.literal layout (.state index)).weakenAt 0)
      (encode layout (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

variable {checked : Checked} {base : Base checked}
  (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {allocationGlobals : Nat}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame allocationGlobals
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[allocationGlobals]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)


include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller acceptedHook actualTyped in
/-- The original hook completion supplies a strict parameter prefix, followed
by its real marked allocation receipt. No continuation agreement supplies a size. -/
theorem hook_prefix_with_spine {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata bodyStore prefixSize,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      prefixSize < size ∧ finalStore = bodyStore.set location (encode prepared.layout.frame current) ∧
      (∃ entry : Prefix prepared.layout.frame allocationGlobals location (.state index) values functions registry
        function context bindings arguments before (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative (.unit :: prepared.layout.frame.type :: actualContext)
        (.unit :: encode prepared.layout.frame current :: actual)
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        parameterCode body prefixSize value bodyStore,
        ∃ added : Environment, added.length = bindings.length ∧
          entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical) := by
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ := CallableIndexedFormation.namedBody_history prepared acceptedHook
  have renamed : code.rename ξ = SourceCoreCallableIndexedFrames.withFrame
      (.var (ξ (base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal prepared.layout.frame (.state index)) (parameterCode.rename ξ) := by
    rw [emitted, withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  rw [renamed] at evaluation
  obtain ⟨nextSize, prefixSize, nextValue, nextStore, bodyStore, nextEvaluation, prefixEvaluation,
    _, smaller, finalEq⟩ := RecursiveNamedCallBounds.with_frame (.var actualReference) caller.read evaluation
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic nextEvaluation.sound
    (next_evaluates prepared.layout.frame index actual store (encode prepared.layout.frame current))
  rw [← rename_prefix] at prefixEvaluation
  obtain ⟨installedHeaps, installedCaller⟩ := CallableIndexedBodyFrames.install registered heaps unmapped typed caller (.stable history)
  obtain ⟨entry, added, length, spine⟩ := parameter_prefix_with_spine functions onError acceptedPrefix parameters inputs extended definitions registered represented
    environments installedHeaps initialLocals (agree_prefix actualLayout (encode prepared.layout.frame current))
    (RuntimeEnvironmentHasTypes.cons .unit
      (.cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world registered current) actualTyped))
    canonicalReference installedCaller.read unmapped prefixEvaluation
  exact ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, entry, added, length, spine⟩


include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller acceptedHook actualTyped in
theorem hook_prefix {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata bodyStore prefixSize,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      prefixSize < size ∧ finalStore = bodyStore.set location (encode prepared.layout.frame current) ∧
      Nonempty (Prefix prepared.layout.frame allocationGlobals location (.state index) values functions registry
        function context bindings arguments before (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative (.unit :: prepared.layout.frame.type :: actualContext)
        (.unit :: encode prepared.layout.frame current :: actual)
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        parameterCode body prefixSize value bodyStore) := by
  obtain ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, entry, _⟩ :=
    hook_prefix_with_spine (prepared := prepared) (functions := functions) (onError := onError)
      (parameters := parameters) (inputs := inputs) (extended := extended) (acceptedPrefix := acceptedPrefix)
      (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference)
      (actualReference := actualReference) (unmapped := unmapped) (typed := typed) (caller := caller) evaluation
  exact ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, ⟨entry⟩⟩


variable {expressionSyntax : ExpressionId → Prop}
  (profile : Body layouts owner active prepared.layout.frame allocationGlobals onError values function
    expressionSyntax readFuel solved reasonAt ambient
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) context
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) output body fellThrough escaped registry faults)
  (escapedFault : faults .controlEscapedFunction escaped)

include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped
  extension uninitialized missing faithful functionLeaves functionTypes profile escapedFault in
/-- The concrete runtime body closes the shared native hook continuation. -/
theorem hook_preserves {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before function.parameters arguments environment bound)
    (trace : FunctionCallBody.Trace program function context environment bound outcome after) :
    ∃ origin index metadata value finalStore finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  exact BuiltinNamedCalls.hook_preserves_with (prepared := prepared) (functions := functions) (program := program)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots)
    (fun {_ _ _ _ _} entry {_ _} trace => BuiltinNamedCalls.Parameters.preserves_with (functions := functions) (program := program) entry
      (fun bodyTrace => profile.preserves functions definitions registered extension program faithful
        functionLeaves functionTypes uninitialized missing escapedFault entry.environments entry.heaps
        entry.locals entry.lookups entry.actualTyped entry.reference entry.read entry.unmapped bodyTrace) trace)
    allocated trace

include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped
  extension uninitialized missing faithful functionLeaves functionTypes profile escapedFault in
/-- Reflection uses the original strict hook child and its actual allocation
prefix; source execution receives its own independent grade. -/
theorem hook_reflects_sized {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ origin index metadata environment bound outcome after finalMap finalWorld,
      prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      FunctionCallBody.Trace program function context environment bound outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome := by
  obtain ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, ⟨entry⟩⟩ :=
    hook_prefix (prepared := prepared) (functions := functions)
    (onError := onError) (parameters := parameters) (inputs := inputs) (extended := extended)
    (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered)
    (acceptedHook := acceptedHook) (represented := represented) (environments := environments)
    (heaps := heaps) (initialLocals := initialLocals) (actualLayout := actualLayout)
    (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
    (unmapped := unmapped) (typed := typed) (caller := caller) evaluation
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, related, finalHeaps,
    maps, worlds, frame, sourceMetadata, reached⟩ :=
    profile.reflects_sized functions definitions registered extension program faithful functionLeaves functionTypes
      uninitialized missing escapedFault size entry.childSize (Nat.le_trans entry.bounded (Nat.le_of_lt smaller))
      entry.environments entry.heaps entry.locals entry.lookups entry.actualTyped entry.reference entry.read
      entry.unmapped entry.completed
  exact BuiltinNamedCalls.hook_reflects_from_prefix (prepared := prepared) (functions := functions)
    (program := program) (registered := registered) (heaps := heaps) (unmapped := unmapped) (typed := typed)
    (caller := caller) (snapshots := snapshots) owned history finalEq
    (fun _ _ => ⟨entry.environment, entry.heap, outcome, after, finalMap, finalWorld, entry.allocation,
      sourceTrace.sound, related, finalHeaps, entry.maps.trans maps, entry.worlds.trans worlds,
      entry.frame.trans frame, entry.metadata.trans sourceMetadata, reached⟩)

open CallableCoercionMethodFrame (BodyOutcome)

variable {sourceBody : Dynamic.BodyInstance}
  (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)

include profile parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame escapedFault in
/-- Independent method body execution drives the actual marked parameters,
frame install, concrete body and restoration. The selected evidence is fixed. -/
theorem preserves {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : BodyOutcome program sourceBody function.evidence before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  apply CallableCoercionMethodBody.preserves_with (prepared := prepared) (functions := functions) (program := program)
    (parameters := parameters) (extended := extended) (represented := represented) (sourceFrame := sourceFrame)
    (trace := trace)
  intro environment bound after outcome allocated bodyTrace
  obtain ⟨_, _, _, value, finalStore, finalMap, finalWorld, _, _, evaluated, related,
    finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots, _⟩ :=
    hook_preserves
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (profile := profile) (escapedFault := escapedFault) (parameters := parameters) (inputs := inputs)
      (extended := extended) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots) allocated bodyTrace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds,
    frame, metadata, finalCaller, finalSnapshots⟩

include profile parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook extension
  uninitialized missing faithful functionLeaves functionTypes actualTyped sourceFrame escapedFault in
/-- A completed real hook supplies source allocation and a concrete body
trace. Source method invocation follows without ordinary global instantiation. -/
theorem reflects_sized {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program sourceBody function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨_, _, _, environment, bound, outcome, after, finalMap, finalWorld, _, _, allocated, trace,
    related, finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots, _⟩ :=
    hook_reflects_sized
      (prepared := prepared) (functions := functions) (extension := extension) (program := program)
      (onError := onError) (profile := profile) (escapedFault := escapedFault) (parameters := parameters) (inputs := inputs)
      (extended := extended) (uninitialized := uninitialized)
      (missing := missing) (faithful := faithful) (functionLeaves := functionLeaves) (functionTypes := functionTypes)
      (acceptedPrefix := acceptedPrefix) (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference) (actualReference := actualReference)
      (unmapped := unmapped) (typed := typed) (caller := caller) (snapshots := snapshots) completed
  exact CallableCoercionMethodBody.reflects_with (prepared := prepared) (functions := functions) (program := program)
    (extended := extended) (sourceFrame := sourceFrame)
    ⟨environment, bound, outcome, after, finalMap, finalWorld, allocated, trace,
      related, finalHeaps, maps, worlds, frame, metadata, finalCaller, finalSnapshots⟩


end Hook


section Actual

/-- The source method remains independent of the ordinary function catalogue.
This view uses the actual compiled ordered statement roots and full dictionary. -/
abbrev methodFunction {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (sourceBody : Dynamic.BodyInstance) (dictionary : Dynamic.EvidenceEnvironment) : Dynamic.Closure :=
  CallableCoercionMethodFrame.view sourceBody dictionary compiled.statements

/-- Only static source and compiler receipts. The actual compilation fixes the
body, ordered binders, hook, diagnostics and emitted closure. -/
structure Profile {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (values : SourceCoreCompatibleValues.Context) (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (sourceBody : Dynamic.BodyInstance) (dictionary : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named
  parameters : sourceBody.source.inputs = named.inputs.map Prod.fst
  sourceFrame : CallableCoercionMethodFrame.Frame sourceBody (methodFunction compiled sourceBody dictionary)
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend sourceBody.source.owner sourceBody.context sourceBody.source.inputs types context
  expressionSyntax : ExpressionId → Prop
  readFuel : Nat
  body : Body prepared.layouts named.signature.key [] prepared.ancestry.layout.frame prepared.base.globals.length
    (fun error => .sourceAllocation (reprStr error)) values (methodFunction compiled sourceBody dictionary)
    expressionSyntax readFuel named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
    ambient (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) context
    (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) named.signature.resultType compiled.body
    compiled.own.fellThroughReason compiled.own.table.escapedReason registry faults
  definitions : prepared.layouts.definitions = ambient.definitions
  registered : prepared.ancestry.layout.frame.Registered ambient.definitions
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : Profile compiled values ambient sourceBody dictionary administrative registry faults)

/-- Source attribution comes from the actual trait-method judgment. Native
signature equality does not create it. -/
def Profile.of_selected {program : Program} {callerContext : SourceSemantics.Context}
    {callerEvidence : Dynamic.EvidenceEnvironment} {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected program callerContext callerEvidence traitName methodName requirements sourceBody dictionary)
    (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named)
    (parameters : sourceBody.source.inputs = named.inputs.map Prod.fst)
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (extended : MonoBindersExtend sourceBody.source.owner sourceBody.context sourceBody.source.inputs types context)
    {expressionSyntax : ExpressionId → Prop} {readFuel : Nat}
    (body : Body prepared.layouts named.signature.key [] prepared.ancestry.layout.frame prepared.base.globals.length
      (fun error => .sourceAllocation (reprStr error)) values (methodFunction compiled sourceBody dictionary)
      expressionSyntax readFuel named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key)
      ambient (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) context
      (named.inputs.reverse.map fun binding => (binding.1.id, binding.2)) named.signature.resultType compiled.body
      compiled.own.fellThroughReason compiled.own.table.escapedReason registry faults)
    (definitions : prepared.layouts.definitions = ambient.definitions)
    (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
    (parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd)) :
    Profile compiled values ambient sourceBody dictionary administrative registry faults :=
  ⟨sameSource, parameters, CallableCoercionMethodFrame.of_selected selected compiled sameSource.symm,
    context, types, extended, expressionSyntax, readFuel, body, definitions, registered, parameterType⟩

/-- The observed installed closure and both administrative histories are kept
at the actual caller heap. No execution meaning is stored here. -/
structure Installed (functions : FunctionModel values.checked.catalog ambient)
    (mapping : LocationMap) (world : StoreTyping) (before : Dynamic.Heap) (store : Store)
    (callerEnvironment : Environment) where
  canonical : Environment
  captured : Environment
  capturedContext : Core.Context
  embedding : Renaming
  environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions
  locals : Dynamic.EnvironmentAgrees before sourceBody.context.locals []
  captureLayout : EnvironmentsAgree embedding canonical captured
  captureTyped : RuntimeEnvironmentHasTypes world captured capturedContext ambient.definitions
  frameLocation : Location
  canonicalReference : canonical[prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type frameLocation)
  capturedReference : captured[embedding prepared.base.globals.length]? = some (.cellRef prepared.ancestry.layout.frame.type frameLocation)
  unmapped : frameLocation ∉ mapping
  frameTyped : world[frameLocation]? = some prepared.ancestry.layout.frame.type
  current : NativeFrame
  currentGhost : GhostFrame
  caller : CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
    frameLocation current currentGhost store
  records : List CallableIndexedSnapshots.Record
  snapshots : CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
    prepared.ancestry.layout.frame mapping store records
  globalIndex : Nat
  globalLocation : Location
  globalUnmapped : globalLocation ∉ mapping
  globalReference : callerEnvironment[globalIndex]? = some
    (.cellRef (OptionalCell.cellType named.signature.functionType) globalLocation)
  globalRead : store.read? globalLocation = some (.inRight .unit
    (.closure named.signature.parameterType (LanguageResult.resultType named.signature.resultType)
      (compiled.output.rename embedding.lift) captured))

variable (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)

include profile in
private theorem actual_parameters : SourceCoreSourceCells.bindParameters
    (CallableIndexedNamedGeneration.allocator prepared named) sourceBody.source [] named.inputs
    named.signature.resultType SourceCoreFunctions.argumentProjection compiled.body = .ok compiled.parameterCode := by
  rw [profile.sameSource]; exact compiled.parametersCompiled

include profile extension faithful observations functionTypes uninitialized missing escaped in
theorem Profile.preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (trace : NamedCalls.BodyOutcome program sourceBody dictionary before arguments outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (compiled.output.rename installed.embedding.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedMethodRuntimeMeaning.preserves (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
    (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
    (allocationGlobals := prepared.base.globals.length) (functions := functions) (extension := extension) (program := program)
    (onError := fun error => .sourceAllocation (reprStr error)) (profile := profile.body) (escapedFault := escaped)
    (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
    (uninitialized := uninitialized) (missing := missing) (faithful := faithful)
    (functionLeaves := observations) (functionTypes := functionTypes)
    (acceptedPrefix := actual_parameters compiled profile) (definitions := profile.definitions) (registered := profile.registered)
    (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
    (heaps := heaps) (initialLocals := installed.locals)
    (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
    (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
    (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
    (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller)
    (snapshots := installed.snapshots) (sourceFrame := profile.sourceFrame) trace

include profile extension faithful observations functionTypes uninitialized missing escaped in
theorem Profile.reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (compiled.output.rename installed.embedding.lift) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  exact CallablePreparedMethodRuntimeMeaning.reflects_sized (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
    (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
    (allocationGlobals := prepared.base.globals.length) (functions := functions) (extension := extension) (program := program)
    (onError := fun error => .sourceAllocation (reprStr error)) (profile := profile.body) (escapedFault := escaped)
    (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
    (uninitialized := uninitialized) (missing := missing) (faithful := faithful)
    (functionLeaves := observations) (functionTypes := functionTypes)
    (acceptedPrefix := actual_parameters compiled profile) (definitions := profile.definitions) (registered := profile.registered)
    (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
    (heaps := heaps) (initialLocals := installed.locals)
    (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
    (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
    (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
    (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller)
    (snapshots := installed.snapshots) (sourceFrame := profile.sourceFrame) completed

end Actual

section ConcreteCall
private theorem values_arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)


variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Only actual argument effects transport the installed global and caller
frame. No source identity is inferred from the closure's native type. -/
def Installed.extend {functions : FunctionModel values.checked.catalog ambient}
    {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {before after : Dynamic.Heap} {store futureStore : Store} {callerEnvironment : Environment}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld)
    (preserved : AdministrativePreserved mapping store futureMapping futureStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions futureMapping futureWorld after futureStore callerEnvironment := by
  have frameBound := (List.getElem?_eq_some_iff.mp installed.caller.read).1
  have globalBound := (List.getElem?_eq_some_iff.mp installed.globalRead).1
  have frame := preserved installed.frameLocation installed.unmapped frameBound
  have global := preserved installed.globalLocation installed.globalUnmapped globalBound
  exact { installed with
    environments := installed.environments.extend maps worlds
    locals := installed.locals.mono metadata
    captureTyped := installed.captureTyped.weaken worlds
    unmapped := frame.1
    frameTyped := worlds.lookup installed.frameTyped
    caller := ⟨frame.2.trans installed.caller.read, installed.caller.history⟩
    snapshots := installed.snapshots.transport preserved
    globalUnmapped := global.1
    globalRead := global.2.trans installed.globalRead }

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope ids (named.inputs.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = named.inputs.map Prod.snd)
  (packedType : named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes packedType profile in
/-- The first failing argument skips the installed body; successful ordered
arguments enter the same concrete method profile at their actual final heap. -/
theorem call_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
      before ids sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates callerEnvironment store (SourceCoreCalls.call named.signature installed.globalIndex
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have argumentMeaning : TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionBuiltinRuntime.preserves functions extension faithful observations functionTypes
      program callerEvidence callerValid.ledger callerValid.runtime unique callerUninitialized callerMissing
  cases execution with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluation, matched, finalHeaps, maps, worlds, frame, metadata⟩ :=
      TypedDataExpressionSequence.preserves_fault children argumentMeaning environments heaps locals layout actualTyped failed
    have evaluated := SourceCoreCalls.call_argument_failure (signature := named.signature) (index := installed.globalIndex)
      (internalReason := reason) (packedType.symm ▸ argumentsEvaluation)
    have frameRead := (frame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata,
      ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport frame⟩
  | apply argumentsEvaluated bodyExecuted =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentsEvaluation, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
      TypedDataExpressionSequence.preserves_values children argumentMeaning environments heaps locals layout actualTyped argumentsEvaluated
    rw [nativeTypes] at represented
    let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
    have related := values_arguments named.inputs represented
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps, bodyMaps, bodyWorlds,
      bodyFrame, bodyMetadata, current, snapshots⟩ :=
      profile.preserves compiled functions extension program faithful observations functionTypes uninitialized missing escaped
        next related middleHeaps bodyExecuted
    have read := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: callerEnvironment) middleStore
        (.var (installed.globalIndex + 1)) (.cellRef (OptionalCell.cellType named.signature.functionType) installed.globalLocation)
        middleStore from .var installed.globalReference) next.globalRead
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentsEvaluation read bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, current, snapshots⟩

private theorem failed_call {signature : SourceCoreCalls.Signature} {index : Nat} {arguments : Expr} {reason : Word}
    {environment : Environment} {before middle after : Store} {token : Word} {value : Value} {size : Nat}
    (argument : Evaluates environment before arguments (.inLeft signature.parameterType (.word token)) middle)
    (completed : EvaluationSize size environment before (SourceCoreCalls.call signature index arguments reason) value after) :
    value = .inLeft signature.resultType (.word token) ∧ after = middle := by
  cases completed with
  | caseLeft actual branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic actual.sound argument
    cases same
    cases branch with
    | inLeft payload =>
      cases payload with
      | var found =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at found
        cases found
        exact ⟨rfl, rfl⟩
  | caseRight actual _ => cases (evaluation_deterministic actual.sound argument).1

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes packedType profile in
/-- Original call children supply the argument completion and strict method
body witness. The source trace is reconstructed independently at each step. -/
theorem call_reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {reason : Word} {value : Value} {size : Nat}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (SourceCoreCalls.call named.signature installed.globalIndex
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
        before ids sourceBody outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  obtain ⟨argumentSize, argumentValue, middleStore, argumentStrict, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  have argumentMeaning : TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program callerContext callerEvidence callerSource
      (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt) faults :=
    CompatibleExpressionBuiltinRuntime.reflects functions extension faithful observations functionTypes
      program callerEvidence callerValid.ledger callerValid.runtime callerUninitialized callerMissing
  obtain ⟨argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata⟩ :=
    TypedDataExpressionSequence.reflects children argumentMeaning environments heaps locals layout actualTyped argumentEvaluation.sound
  cases represented with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      obtain ⟨rfl, rfl⟩ := failed_call (packedType.symm ▸ argumentEvaluation.sound) completed
      have frameRead := (argumentFrame installed.frameLocation installed.unmapped (List.getElem?_eq_some_iff.mp installed.caller.read).1).2
      exact ⟨.fault _, middle, middleMap, middleWorld, .argumentFault failed, .fault matched, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata,
        ⟨frameRead.trans installed.caller.read, installed.caller.history⟩, installed.snapshots.transport argumentFrame⟩
  | values represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      let next := installed.extend argumentMaps argumentWorlds argumentFrame argumentMetadata
      have related := values_arguments named.inputs represented
      obtain ⟨bodySize, bodyStrict, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
        argumentEvaluation.sound installed.globalReference next.globalRead completed
      obtain ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, bodyMaps, bodyWorlds,
        bodyFrame, bodyMetadata, current, snapshots⟩ :=
        profile.reflects_sized compiled functions extension program faithful observations functionTypes uninitialized missing escaped
          next related middleHeaps bodyEvaluation
      exact ⟨outcome, after, finalMap, finalWorld, .apply evaluatedArguments bodyTrace, result,
        finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, current, snapshots⟩

end ConcreteCall

section OperatorSource
open CallablePreparedMethodSelection
open CallableCoercionExpressionCertificates (Projector Specialized Lowered rawNode)

variable {checkedProgram : CheckedProgram} {project : Projector} {caller : Specialized}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : Lowered}

/-- Dispatch and the full source selector come from the same actual checker
return. An arbitrary source receipt is never identified by its trait name. -/
structure OperatorSource
    (receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output)
    extends SourceReceipt receipt where
  dispatch : match node.form with
    | .unary operator _ => UnaryTraitDispatch operator traitName methodName
    | .binary _ operator _ => BinaryTraitDispatch operator traitName methodName
    | _ => False

private theorem unary_dispatch {operator : Syntax.UnaryOp} {traitName methodName : String}
    (accepted : Detail.unaryOperatorDispatch operator = .traitMethod traitName methodName) :
    UnaryTraitDispatch operator traitName methodName := by
  cases operator <;> cases accepted <;> constructor

private theorem binary_dispatch {operator : Syntax.BinaryOp} {traitName methodName : String}
    (accepted : Detail.binaryOperatorDispatch operator = .traitMethod traitName methodName) :
    BinaryTraitDispatch operator traitName methodName := by
  cases operator <;> cases accepted <;> constructor

/-- Reuse the real unary/binary method certificate and retain its dispatch. -/
theorem OperatorSource.of_accepted
    (receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output) :
    Nonempty (OperatorSource receipt) := by
  have accepted := receipt.selectedMethod
  have rawRequirements : SourceCompilationPlan.ordinaryOwnedRequirements? (rawNode node receipt.requirements) =
      some receipt.requirements := by
    change (if receipt.requirements.length < 0 then none else
      if receipt.requirements = receipt.requirements.take (receipt.requirements.length - 0) ++ [] then
        some (receipt.requirements.take (receipt.requirements.length - 0)) else none) = some receipt.requirements
    simp
  rcases receipt.form with ⟨operator, operand, form, _⟩ | ⟨operator, left, right, form, _⟩
  · simp only [form] at accepted
    obtain ⟨traitName, methodName, methodIds, dispatch, owned, ⟨certificate⟩⟩ := unary_of_accepted accepted
    exact ⟨⟨⟨traitName, methodName, methodIds, 1,
      Option.some.inj (rawRequirements.symm.trans owned), certificate⟩, by simpa only [form] using unary_dispatch dispatch⟩⟩
  · simp only [form] at accepted
    obtain ⟨traitName, methodName, methodIds, dispatch, owned, ⟨certificate⟩⟩ := binary_of_accepted accepted
    exact ⟨⟨⟨traitName, methodName, methodIds, 1,
      Option.some.inj (rawRequirements.symm.trans owned), certificate⟩, by simpa only [form] using binary_dispatch dispatch⟩⟩

private theorem binary_strict {operator : Syntax.BinaryOp} {traitName methodName : String}
    (dispatch : BinaryTraitDispatch operator traitName methodName) : Dynamic.StrictBinaryOperator operator := by
  cases dispatch <;> constructor

variable
  {receipt : Operator checkedProgram project caller compilation child fuel source scope id reasonAt policy node output}
  (selected : OperatorSource receipt)
  {program : Program} {context : SourceSemantics.Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
  {sourceBody : Dynamic.BodyInstance}
  (selection : Dynamic.OperatorMethodSelected program context evidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)

include selected selection in
/-- This pure bridge builds the actual source operator judgment from the same
ordered argument trace and independently selected method body. -/
theorem OperatorSource.raw {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : NamedCalls.Arguments.Trace program context evidence dictionary source environment before
      receipt.arguments sourceBody outcome after) :
    CallableCoercionExpressionMeaning.RawOutcome program context evidence source environment before node outcome after := by
  have layout : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions receipt.requirements := by
    have owned := receipt.ordinary
    change (let suffix := coercionRequirementIds node.coercions
      if node.requirements.length < suffix.length then none else
        let owned := node.requirements.take (node.requirements.length - suffix.length)
        if node.requirements = owned ++ suffix then some owned else none) = some receipt.requirements at owned
    dsimp only at owned
    split at owned
    · contradiction
    · split at owned
      · have same := Option.some.inj owned
        change node.requirements = receipt.requirements ++ coercionRequirementIds node.coercions
        rw [← same]
        exact ‹node.requirements = _›
      · contradiction
  have dispatch := selected.dispatch
  rcases receipt.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
  · simp only [form] at dispatch
    rw [arguments] at trace
    cases trace with
    | argumentFault fault =>
      cases fault with
      | head fault =>
        dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
        rw [form]
        exact .unaryOperand layout fault
      | tail _ fault => cases fault
    | apply evaluated body =>
      cases evaluated with
      | cons operandEvaluated remaining =>
        cases remaining
        cases body with
        | value invoked =>
          dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
          rw [form]
          exact .unary layout operandEvaluated (.method dispatch selection invoked)
        | fault failed =>
          dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
          rw [form]
          exact .unaryApply layout operandEvaluated (.method dispatch selection failed)
  · simp only [form] at dispatch
    rw [arguments] at trace
    cases trace with
    | argumentFault fault =>
      cases fault with
      | head fault =>
        dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
        rw [form]
        exact .binaryLeft layout fault
      | tail leftEvaluated fault =>
        cases fault with
        | head fault =>
          dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
          rw [form]
          exact .binaryRight layout leftEvaluated (.strict (binary_strict dispatch)) fault
        | tail _ fault => cases fault
    | apply evaluated body =>
      cases evaluated with
      | cons leftEvaluated remaining =>
        cases remaining with
        | cons rightEvaluated remaining =>
          cases remaining
          cases body with
          | value invoked =>
            dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
            rw [form]
            exact .binaryEvaluateRight layout leftEvaluated
              (.strict (binary_strict dispatch)) rightEvaluated (.method dispatch selection invoked)
          | fault failed =>
            dsimp only [CallableCoercionExpressionMeaning.RawOutcome]
            rw [form]
            exact .binaryApply layout leftEvaluated
              (.strict (binary_strict dispatch)) rightEvaluated (.method dispatch selection failed)

include selected selection in
/-- The old whole-expression entry adds the empty coercion path to the same
raw operator proof. The raw proof retains the original ordered requirements. -/
theorem OperatorSource.expression {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (coercions : node.coercions = [])
    (trace : NamedCalls.Arguments.Trace program context evidence dictionary source environment before
      receipt.arguments sourceBody outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  have raw := selected.raw selection trace
  cases outcome with
  | value value =>
    exact .value (.intro (lookupExpression?_sound receipt.found) raw (coercions ▸ .nil))
  | fault reason => exact .fault (.form (lookupExpression?_sound receipt.found) raw)

end OperatorSource

section EmittedOperator
open CallableCoercionExpressionCertificates

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  (profile : Profile compiled values ambient sourceBody dictionary administrative registry faults)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (diagnostics.reasonAt named.signature.key id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((diagnostics.reasonAt named.signature.key id).add tag))
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  {callerSource : TypedSource} {callerContext : SourceSemantics.Context}
  {callerEvidence : Dynamic.EvidenceEnvironment} {callerSolved : List SolvedRequirement}
  {callerReasonAt : ExpressionId → Word} {readFuel : Nat}
  (callerValid : CompatibleRuntimeContextValidity.Valid callerSolved callerContext callerEvidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (callerReasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((callerReasonAt id).add tag))
  {checkedProgram : CheckedProgram} {project : CallableCoercionExpressionCertificates.Projector}
  {caller : SourceSpecialization.SpecializedFunction} {compilation : SourceCoreFunctions.Context}
  {child : SourceCoreEvidence.Child} {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {policy : SourceCoreFunctions.CallablePolicy} {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallablePreparedMethodSelection.Operator checkedProgram project caller compilation child fuel
    callerSource scope id callerReasonAt policy node output)

/-- Full retained method and dictionary equality accompany the real compiled
closure. Signature equality alone never supplies method source attribution. -/
structure OperatorAlignment : Prop where
  retained : named.specialized = receipt.selection.method.specialized
  sourceBody : sourceBody = CallableCoercionMethodInstantiation.bodyInstance checkedProgram receipt.selection.method
  dictionary : dictionary = CallableNamedMetadata.environment receipt.dictionary
  signature : receipt.native.signature = named.signature

variable (alignment : OperatorAlignment (named := named) (sourceBody := sourceBody) (dictionary := dictionary) receipt)
  (selected : OperatorSource receipt)
  (selection : Dynamic.OperatorMethodSelected program callerContext callerEvidence selected.traitName selected.methodName
    receipt.requirements sourceBody dictionary)
  (children : DataExpressionSequence.Tree callerSource
    (CompatibleExpressionBuiltinRuntime.Certificate readFuel values callerSource callerContext callerSolved callerReasonAt)
    scope receipt.arguments (named.inputs.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
  (nativeTypes : receipt.loweredArguments.map (·.type) = named.inputs.map Prod.snd)

include alignment in
/-- The actual operator operand is the issued method call, independently of
its retained output-coercion suffix. -/
theorem OperatorAlignment.operand_emitted (ξ : Renaming) :
    receipt.operand.expression.rename ξ = SourceCoreCalls.call named.signature
      (ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
      ((SourceCoreCalls.packArguments receipt.loweredArguments).expression.rename ξ) compilation.internalReason := by
  simpa only [NamedCalls.Arguments.call_rename, alignment.signature] using
    congrArg (fun value : SourceCoreBasic.LoweredExpr => value.expression.rename ξ) receipt.native.emitted

include alignment in
/-- The original suffix receipt is still retained. This final-expression
consumer handles the explicit empty suffix only. -/
theorem OperatorAlignment.emitted (coercions : node.coercions = []) (ξ : Renaming) :
    output.expression.rename ξ = SourceCoreCalls.call named.signature
      (ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
      ((SourceCoreCalls.packArguments receipt.loweredArguments).expression.rename ξ) compilation.internalReason := by
  have suffix := receipt.suffix.accepted
  rw [coercions] at suffix
  have same : receipt.operand = output := Except.ok.inj suffix
  exact (congrArg (fun value : SourceCoreBasic.LoweredExpr => value.expression.rename ξ) same.symm).trans
    (alignment.operand_emitted receipt ξ)

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection in
theorem operator_preserves {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap}
    {store : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (coercions : node.coercions = [])
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (unique : NodeOccurrencesUnique callerSource)
    (execution : NamedCalls.Arguments.Trace program callerContext callerEvidence dictionary callerSource sourceEnvironment
      before receipt.arguments sourceBody outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      Evaluates callerEnvironment store (output.expression.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have packedType : named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have emitted := alignment.emitted receipt coercions ξ
  rw [← located] at emitted
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    call_preserves compiled profile functions extension program faithful observations functionTypes uninitialized missing escaped
      callerValid callerUninitialized callerMissing children nativeTypes packedType
      installed environments heaps locals layout actualTyped unique execution
  exact ⟨value, finalStore, finalMap, finalWorld, selected.expression selection coercions execution,
    emitted.symm ▸ evaluated, rest⟩

include extension faithful observations functionTypes uninitialized missing escaped callerValid callerUninitialized callerMissing
  children nativeTypes profile alignment selected selection in
theorem operator_reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment canonical : Environment}
    {callerAdministrative actualContext : Core.Context} {sourceEnvironment : Dynamic.Environment}
    {ξ : Renaming} {value : Value} {size : Nat}
    (coercions : node.coercions = [])
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative)
      functions mapping world before store callerEnvironment)
    (located : installed.globalIndex = ξ (scope.length + compilation.administrativePrefix + receipt.native.index))
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
      callerAdministrative scope sourceEnvironment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before callerContext.locals sourceEnvironment)
    (layout : EnvironmentsAgree ξ canonical callerEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world callerEnvironment actualContext ambient.definitions)
    (completed : EvaluationSize size callerEnvironment store (output.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program callerContext callerEvidence callerSource sourceEnvironment before id outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have packedType : named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
    simpa only [alignment.signature] using receipt.native.inputType
  have emitted := alignment.emitted receipt coercions ξ
  rw [← located] at emitted
  rw [emitted] at completed
  obtain ⟨outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    call_reflects_sized compiled profile functions extension program faithful observations functionTypes uninitialized missing escaped
      callerValid callerUninitialized callerMissing children nativeTypes packedType
      installed environments heaps locals layout actualTyped completed
  exact ⟨outcome, after, finalMap, finalWorld, selected.expression selection coercions trace, rest⟩

end EmittedOperator

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogEntries
/-! Actual method prefixes retain a separately supplied finite catalog. The
marked allocator supplies the exact added cells and packed argument slot; the
real hook supplies its named history. Source method attribution remains a
separate frame receipt, without ordinary function instantiation. No method body
grammar or execution correspondence is required by these catalog transports. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogEntries
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames
open CallablePreparedMethodRuntimeMeaning

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}

/-- Source attribution, actual named history, and catalog authority are kept as
independent receipts. The dictionary is the one in the original closure view. -/
structure SourceEntry (named : SourceCoreGeneralFunctions.Function)
    (sourceBody : Dynamic.BodyInstance) (function : Dynamic.Closure)
    (headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program))
    (capturePrefix callerPrefix : Nat) (scope : SourceCoreLocalCell.Scope)
    (mapping : LocationMap) (world : StoreTyping) (heap : Dynamic.Heap) (store : Store) (canonical : Environment) where
  catalog : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical
  sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function
  sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named
  origin : Word
  metadata : MetadataState
  owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin
  ghost : catalog.authority.ghost = .named origin
  carried : Carries prepared.graph.inputs prepared.graph.table catalog.authority.current (.named origin) (some metadata)
  reference : canonical[scope.length + 1 + base.globals.length]? =
    some (.cellRef prepared.layout.frame.type catalog.authority.frameLocation)

variable {named : SourceCoreGeneralFunctions.Function} {sourceBody : Dynamic.BodyInstance} {function : Dynamic.Closure}

def SourceEntry.extend {scope : SourceCoreLocalCell.Scope} {mapping futureMap : LocationMap}
    {world futureWorld : StoreTyping} {heap after : Dynamic.Heap} {store futureStore : Store} {canonical : Environment}
    (entry : SourceEntry named sourceBody function headers locations capturePrefix callerPrefix scope mapping world heap store canonical)
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping store futureMap futureStore)
    (metadata : Dynamic.HeapMetadataExtend heap after) :
    SourceEntry named sourceBody function headers locations capturePrefix callerPrefix scope futureMap futureWorld after futureStore canonical :=
  { entry with catalog := entry.catalog.extend maps worlds frame metadata }

def protectedEntry (named : SourceCoreGeneralFunctions.Function) (sourceBody : Dynamic.BodyInstance)
    (function : Dynamic.Closure) (headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program)
    (locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program))
    (capturePrefix callerPrefix : Nat) : ProtectedExpressionMeaning.Entry :=
  fun scope mapping world heap store canonical =>
    Nonempty (SourceEntry named sourceBody function headers locations capturePrefix callerPrefix scope mapping world heap store canonical)

theorem transport : ProtectedExpressionMeaning.Transport
    (protectedEntry named sourceBody function headers locations capturePrefix callerPrefix) := by
  constructor
  intro scope mapping world heap store canonical futureMap futureWorld after futureStore entry maps worlds frame metadata
  obtain ⟨entry⟩ := entry
  exact ⟨entry.extend maps worlds frame metadata⟩

theorem binds : ProtectedExpressionMeaning.Binds
    (protectedEntry named sourceBody function headers locations capturePrefix callerPrefix) := by
  constructor
  all_goals
    intro scope mapping world heap store canonical id type value entry
    obtain ⟨entry⟩ := entry
    refine ⟨{ entry with catalog := ⟨entry.catalog.authority, ?_⟩, reference := ?_ }⟩
    · intro header member
      have index : ((id, type) :: scope).length + callerPrefix + header.slot =
          (scope.length + callerPrefix + header.slot) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using entry.catalog.globals header member
    · have index : ((id, type) :: scope).length + 1 + base.globals.length =
          (scope.length + 1 + base.globals.length) + 1 := by simp only [List.length_cons]; omega
      simpa only [index, List.getElem?_cons_succ] using entry.reference

section Effects
variable {bindings : List Binding} {nativeArguments : List Value}
  {mapping prefixMap : LocationMap} {world prefixWorld : StoreTyping}
  {before prefixHeap : Dynamic.Heap} {store prefixStore : Store}
  {canonical prefixCanonical added : Environment} {location : Location} {next : NativeFrame}
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  (maps : LocationMap.Extends mapping prefixMap) (worlds : WorldExtends world prefixWorld)
  (frame : AdministrativePreserved mapping (store.set location (encode prepared.layout.frame next)) prefixMap prefixStore)
  (metadata : Dynamic.HeapMetadataExtend before prefixHeap)
  (length : added.length = bindings.length)
  (spine : prefixCanonical = added ++ DataPatternValues.packValues nativeArguments :: canonical)

/-- Actual installation and prefix effects suffice before any body completion.
The ordered spine retains the packed slot and every original catalog row. -/
def catalog_entry_of_effects {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    RecursiveNamedCatalog.Entry headers locations capturePrefix (callerPrefix + 1)
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) prefixMap prefixWorld
      prefixHeap prefixStore prefixCanonical := by
  let installed := initial.authority.install history
  have effects : AdministrativePreserved mapping
      (store.set initial.authority.frameLocation (encode prepared.layout.frame next)) prefixMap prefixStore := by
    simpa only [sameFrame] using frame
  refine ⟨installed.extend maps worlds effects metadata, ?_⟩
  intro header member
  rw [spine]
  simp only [List.length_map, List.length_reverse]
  have index : bindings.length + (callerPrefix + 1) + header.slot =
      added.length + (callerPrefix + header.slot + 1) := by omega
  rw [index, List.getElem?_append_right (by omega)]
  simpa only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.length_nil, Nat.zero_add]
    using initial.globals header member

/-- Source attribution and actual carried history remain separate inputs.
No native evaluation or type creates the source method frame. -/
def source_entry_of_effects {origin : Word} {state : MetadataState}
    (reference : prefixCanonical[(bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + base.globals.length]? =
      some (.cellRef prepared.layout.frame.type location))
    (owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (history : Carries prepared.graph.inputs prepared.graph.table next (.named origin) (some state))
    (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
    (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named) :
    SourceEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1)
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) prefixMap prefixWorld
      prefixHeap prefixStore prefixCanonical :=
  { catalog := catalog_entry_of_effects initial sameFrame maps worlds frame metadata length spine (.stable history)
    sourceFrame, sameSource, origin, metadata := state, owned
    ghost := rfl
    carried := history
    reference := by
      change prefixCanonical[_]? = some (Value.cellRef prepared.layout.frame.type initial.authority.frameLocation)
      simpa only [sameFrame] using reference }
end Effects

section Prefix
variable {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {bindings : List Binding} {arguments : List Dynamic.Value}
  {nativeArguments : List Value} {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
  {parameterCode body : Expr} {size : Nat} {result : Value} {bodyStore : Store}
  {location : Location} {next : NativeFrame}
  (reached : Prefix prepared.layout.frame base.globals.length location next values functions registry function context bindings
    arguments before (store.set location (encode prepared.layout.frame next)) mapping world administrative actualContext
    actual ξ parameterCode body size result bodyStore)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = bindings.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical)

/-- Installation and the original prefix effects preserve every catalog row.
The extra packed-argument slot increases only the caller offset. -/
def catalog_entry {nextGhost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next nextGhost) :
    RecursiveNamedCatalog.Entry headers locations capturePrefix (callerPrefix + 1)
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) reached.mapping reached.world
      reached.heap reached.store reached.canonical :=
  catalog_entry_of_effects initial sameFrame reached.maps reached.worlds reached.frame reached.metadata length spine history

/-- The actual hook's owned key and complete history are joined to the
independent trait-method frame. The source dictionary is never reconstructed. -/
def source_entry {origin : Word} {metadata : MetadataState}
    (owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
    (history : Carries prepared.graph.inputs prepared.graph.table next (.named origin) (some metadata))
    (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
    (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named) :
    SourceEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1)
      (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) reached.mapping reached.world
      reached.heap reached.store reached.canonical :=
  source_entry_of_effects initial sameFrame reached.maps reached.worlds reached.frame reached.metadata length spine
    reached.reference owned history sourceFrame sameSource

include initial sameFrame in
/-- Body effects restore the original caller catalog, including its complete
captures and protected snapshots. No body evaluation or source trace is added. -/
theorem restore_catalog {current : NativeFrame} {currentGhost : GhostFrame}
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
    (registered : prepared.layout.frame.Registered ambient.definitions)
    {finalMap : LocationMap} {finalWorld : StoreTyping} {after : Dynamic.Heap} {finalBodyStore : Store}
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalBodyStore)
    (maps : LocationMap.Extends reached.mapping finalMap) (worlds : WorldExtends reached.world finalWorld)
    (frame : AdministrativePreserved reached.mapping reached.store finalMap finalBodyStore)
    (metadata : Dynamic.HeapMetadataExtend reached.heap after) :
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
      (finalBodyStore.set location (encode prepared.layout.frame current)) ∧
    Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after
      (finalBodyStore.set location (encode prepared.layout.frame current)) canonical) ∧
    AdministrativePreserved mapping store finalMap (finalBodyStore.set location (encode prepared.layout.frame current)) ∧
    CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost
      (finalBodyStore.set location (encode prepared.layout.frame current)) := by
  have unmapped : location ∉ mapping := sameFrame ▸ initial.authority.unmapped
  have typed : world[location]? = some prepared.layout.frame.type := sameFrame ▸ initial.authority.typed
  obtain ⟨finalHeaps, restoredFrame, finalCaller⟩ := CallableIndexedBodyFrames.restore registered unmapped typed caller
    heaps (reached.worlds.trans worlds) (reached.frame.trans frame)
  exact ⟨finalHeaps, ⟨initial.extend (reached.maps.trans maps) (reached.worlds.trans worlds) restoredFrame
    (reached.metadata.trans metadata)⟩, restoredFrame, finalCaller⟩

end Prefix
section ActualHook
variable (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame base.globals.length
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[base.globals.length]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)


include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller acceptedHook actualTyped in
/-- The original completed hook supplies the measured prefix, its exact
packed-argument spine and the catalog at that same body state. Source method
attribution is supplied independently of native history and typing. -/
theorem hook_catalog_entry
    (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
    (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
    (sameFrame : initial.authority.frameLocation = location)
    {size : Nat} {value : Value} {finalStore : Store}
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ index bodyStore prefixSize,
      prefixSize < size ∧ finalStore = bodyStore.set location (encode prepared.layout.frame current) ∧
      ∃ entry : Prefix prepared.layout.frame base.globals.length location (.state index) values functions registry
        function context bindings arguments before (store.set location (encode prepared.layout.frame (.state index))) mapping world
        administrative (.unit :: prepared.layout.frame.type :: actualContext)
        (.unit :: encode prepared.layout.frame current :: actual)
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ))
        parameterCode body prefixSize value bodyStore,
        entry.childSize < size ∧
        (∃ added : Environment, added.length = bindings.length ∧
          entry.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical) ∧
        Nonempty (SourceEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1)
          (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.mapping entry.world
          entry.heap entry.store entry.canonical) := by
  obtain ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, smaller, finalEq, entry, added, length, spine⟩ :=
    hook_prefix_with_spine (prepared := prepared) (functions := functions) (onError := onError)
      (parameters := parameters) (inputs := inputs) (extended := extended) (acceptedPrefix := acceptedPrefix)
      (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference)
      (actualReference := actualReference) (unmapped := unmapped) (typed := typed) (caller := caller) evaluation
  exact ⟨index, bodyStore, prefixSize, smaller, finalEq, entry, Nat.lt_of_le_of_lt entry.bounded smaller,
    ⟨added, length, spine⟩, ⟨source_entry entry initial sameFrame length spine owned history sourceFrame sameSource⟩⟩

end ActualHook

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogEntries
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogBodyMeaning
/-! The actual method prefix supplies the original native body child and the
complete catalog at that same state. The shared kernel reflects that child at
its original dictionary. Body effects then restore the caller's full catalog,
including unused captures and snapshots. The expression premises are internal
bounded induction interfaces; no body execution law or evidence reindexing is
introduced here. Source and native grades remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogBodyMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning
open CallablePreparedMethodCatalogEntries

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {named : SourceCoreGeneralFunctions.Function} {sourceBody : Dynamic.BodyInstance} {function : Dynamic.Closure}
  {functions : FunctionModel values.checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {bindings : List CallableIndexedParameterCertificates.Binding}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {administrative actualContext : Core.Context} {canonical actual : Environment} {ξ : Renaming}
  {parameterCode body : Expr} {size : Nat} {result : Value} {bodyStore : Store}
  {location : Location} {next current : NativeFrame} {currentGhost : GhostFrame}
  (reached : Prefix prepared.layout.frame base.globals.length location next values functions registry function context bindings
    arguments before (store.set location (encode prepared.layout.frame next)) mapping world administrative actualContext
    actual ξ parameterCode body size result bodyStore)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = bindings.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues nativeArguments :: canonical)
  {origin : Word} {metadata : MetadataState}
  (owned : prepared.graph.inputs.callable.table.idAt? (.named named.signature.key) = some origin)
  (history : Carries prepared.graph.inputs prepared.graph.table next (.named origin) (some metadata))
  (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
  (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named)

section Reflection
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {solved : List SolvedRequirement} {output : Ty} {fellThrough escaped : Word}
  {faults : FunctionCalls.FaultRep}
  (kernel : CallableRuntimeBodyKernel.BodyFor layouts owner active prepared.layout.frame base.globals.length onError
    values function expressionSyntax certificates validity diagnosticPolicy ambient
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) context
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) output body fellThrough escaped registry faults)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : prepared.layout.frame.Registered ambient.definitions)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions) (escapedFault : faults .controlEscapedFunction escaped)
  (extend : ∀ {context next binder}, validity context → BinderExtends function.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence)

include initial sameFrame length spine owned history sourceFrame sameSource kernel definitions registered extension
  faithful observations functionTypes escapedFault extend runtimeOf in
/-- Reflect the exact body child extracted from the original hook. The strict
bound is supplied by that hook, even for an empty parameter list. The source
trace, reached method entry, full heap and restored caller catalog are returned
from one kernel invocation and the existing restore proof. -/
theorem reflects_prefix_sized (budget : Nat) (strict : reached.childSize < budget)
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below budget
      (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (certificates context) faults (protectedEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1))))
    (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context reached.environment reached.heap outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after bodyStore ∧
      LocationMap.Extends reached.mapping finalMap ∧ WorldExtends reached.world finalWorld ∧
      AdministrativePreserved reached.mapping reached.store finalMap bodyStore ∧ Dynamic.HeapMetadataExtend reached.heap after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) reached.environment reached.heap after outcome ∧
      Nonempty (SourceEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1)
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) finalMap finalWorld after bodyStore reached.canonical) ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after
        (bodyStore.set location (encode prepared.layout.frame current)) ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after
        (bodyStore.set location (encode prepared.layout.frame current)) canonical) ∧
      AdministrativePreserved mapping store finalMap (bodyStore.set location (encode prepared.layout.frame current)) ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost
        (bodyStore.set location (encode prepared.layout.frame current)) ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧ Dynamic.HeapMetadataExtend before after := by
  let installed := source_entry reached initial sameFrame length spine owned history sourceFrame sameSource
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds,
    frame, metadata, reachedExit, retained⟩ :=
    kernel.reflects_sized functions definitions registered extension program faithful observations functionTypes escapedFault
      (transport (named := named) (sourceBody := sourceBody) (function := function))
      (binds (named := named) (sourceBody := sourceBody) (function := function)) extend runtimeOf
      budget reached.childSize (Nat.le_of_lt strict) expressions reached.environments reached.heaps reached.locals
      reached.lookups reached.actualTyped reached.reference reached.read reached.unmapped ⟨installed⟩ reached.completed
  obtain ⟨restoredHeaps, restoredCatalog, restoredFrame, restoredCaller⟩ :=
    restore_catalog reached initial sameFrame caller registered heaps maps worlds frame metadata
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, heaps, maps, worlds, frame, metadata,
    reachedExit, retained, restoredHeaps, restoredCatalog, restoredFrame, restoredCaller,
    reached.maps.trans maps, reached.worlds.trans worlds, reached.metadata.trans metadata⟩

end Reflection
end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogBodyMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning
/-! The original compiled hook retains its measured parameter prefix. The
same-dictionary body kernel reflects that exact child and restores the complete
caller catalog. Source method attribution is supplied independently; the bounded
expression premise is an internal induction interface, not a closed whole-body
claim. No body execution law is stored in a receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}

variable {sourceBody : Dynamic.BodyInstance}
section Hook
variable (functions : CompatiblePayload.FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {readFuel : Nat} {bindings : List Binding} {output : Ty} {policy : SourceCoreLoops.Policy}
  {fuel : Nat} {fellThrough escaped : Word} {body parameterCode : Expr}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution}
  (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
  (parameters : function.parameters = bindings.map Prod.fst)
  (inputs : function.source.inputs = bindings.map Prod.fst)
  (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
  (unique : NodeOccurrencesUnique function.source) {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, CompatiblePayload.MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (acceptedPrefix : SourceCoreSourceCells.bindParameters
    (SourceCoreCallableIndexedAllocationFrames.allocator prepared.layout.frame base.globals.length
      (layouts.allocatorAt owner active onError)) function.source [] bindings output
    SourceCoreFunctions.argumentProjection body = .ok parameterCode)
  (definitions : layouts.definitions = ambient.definitions) (registered : prepared.layout.frame.Registered ambient.definitions)
  {named : SourceCoreGeneralFunctions.Function} {code : Expr} {ξ : Renaming}
  (acceptedHook : SourceCoreCallableIndexedAncestry.namedBody prepared named parameterCode = .ok code)
  {mapping : LocationMap} {world : StoreTyping} {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    mapping world bindings arguments nativeArguments)
  {administrative actualContext : Core.Context} {canonical actual : Environment} {before : Dynamic.Heap} {store : Store}
  {location : Location} {current : NativeFrame} {currentGhost : GhostFrame}
  {records : List CallableIndexedSnapshots.Record}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world
    administrative [] [] canonical ambient.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
  (initialLocals : Dynamic.EnvironmentAgrees before function.context.locals [])
  (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues nativeArguments :: canonical) actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
  (canonicalReference : canonical[base.globals.length]? = some (.cellRef prepared.layout.frame.type location))
  (actualReference : actual[ξ (base.globals.length + 1)]? = some (.cellRef prepared.layout.frame.type location))
  (unmapped : location ∉ mapping) (typed : world[location]? = some prepared.layout.frame.type)
  (caller : CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost store)
  (snapshots : CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping store records)



variable {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (kernel : CallableRuntimeBodyKernel.BodyFor layouts owner active prepared.layout.frame base.globals.length onError
    values function expressionSyntax certificates validity diagnosticPolicy ambient
    (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) context
    (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) output body fellThrough escaped registry faults)
  (escapedFault : faults .controlEscapedFunction escaped)
  (extend : ∀ {context next binder}, validity context → BinderExtends function.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context → CompatibleRuntimeContextValidity.Valid solved context function.evidence)
  (sourceFrame : CallableCoercionMethodFrame.Frame sourceBody function)
  (sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)

include parameters inputs extended acceptedPrefix definitions registered represented environments heaps initialLocals
  actualLayout canonicalReference actualReference unmapped typed caller snapshots acceptedHook actualTyped kernel extension
  faithful functionLeaves functionTypes escapedFault extend runtimeOf sourceFrame sameSource initial sameFrame in
/-- The body child is extracted from the original completed hook exactly once.
Its independent source trace is lifted through the actual method frame. -/
theorem reflects_hook_sized {size : Nat} {value : Value} {finalStore : Store}
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below size
      (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context function.evidence function.source
        (certificates context) faults (protectedEntry named sourceBody function headers locations capturePrefix (callerPrefix + 1))))
    (evaluation : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before function.parameters arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize function context environment bound outcome after ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody function.evidence before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (bindings.map Prod.snd) :: administrative) program function context
        (bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore canonical) ∧
      CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame location current currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.graph.inputs prepared.graph.table prepared.layout.frame finalMap finalStore records := by
  obtain ⟨origin, index, metadata, bodyStore, prefixSize, owned, history, prefixStrict, finalEq,
    reached, added, length, spine⟩ :=
    hook_prefix_with_spine (prepared := prepared) (functions := functions) (onError := onError)
      (parameters := parameters) (inputs := inputs) (extended := extended) (acceptedPrefix := acceptedPrefix)
      (definitions := definitions) (registered := registered) (acceptedHook := acceptedHook)
      (represented := represented) (environments := environments) (heaps := heaps) (initialLocals := initialLocals)
      (actualLayout := actualLayout) (actualTyped := actualTyped) (canonicalReference := canonicalReference)
      (actualReference := actualReference) (unmapped := unmapped) (typed := typed) (caller := caller) evaluation
  have strict : reached.childSize < size := Nat.lt_of_le_of_lt reached.bounded prefixStrict
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, _, _, _, _, _, reachedExit,
    _, finalHeaps, restoredCatalog, restoredFrame, restoredCaller, maps, worlds, metadata⟩ :=
    CallablePreparedMethodCatalogBodyMeaning.reflects_prefix_sized reached initial sameFrame length spine
      owned history sourceFrame sameSource kernel definitions registered extension faithful functionLeaves functionTypes
      escapedFault extend runtimeOf size strict expressions caller
  have source := sourceFrame.body_of_trace extended reached.allocation trace.sound
  subst finalStore
  exact ⟨sourceSize, reached.environment, reached.heap, outcome, after, finalMap, finalWorld,
    reached.allocation, trace, source, related, finalHeaps, maps, worlds, restoredFrame, metadata,
    reachedExit, restoredCatalog, restoredCaller, snapshots.transport restoredFrame⟩

end Hook
section Compiled

/-- Static attribution and the generic kernel for this actual compilation.
The expression induction interface is supplied to the theorem, not this record. -/
structure ProfileFor {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
    (values : SourceCoreCompatibleValues.Context) (ambient : AmbientDefinitions values.checked.catalog.definitions)
    (sourceBody : Dynamic.BodyInstance) (dictionary : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (expressionSyntax : ExpressionId → Prop) (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (validity : SourceSemantics.Context → Prop) (diagnosticPolicy : AssignmentDiagnosticPolicy) where
  sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named
  parameters : sourceBody.source.inputs = named.inputs.map Prod.fst
  sourceFrame : CallableCoercionMethodFrame.Frame sourceBody (methodFunction compiled sourceBody dictionary)
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend sourceBody.source.owner sourceBody.context sourceBody.source.inputs types context
  body : CallableRuntimeBodyKernel.BodyFor prepared.layouts named.signature.key [] prepared.ancestry.layout.frame
    prepared.base.globals.length (fun error => .sourceAllocation (reprStr error)) values
    (methodFunction compiled sourceBody dictionary) expressionSyntax certificates validity diagnosticPolicy ambient
    (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) context
    (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) named.signature.resultType compiled.body
    compiled.own.fellThroughReason compiled.own.table.escapedReason registry faults
  definitions : prepared.layouts.definitions = ambient.definitions
  registered : prepared.ancestry.layout.frame.Registered ambient.definitions
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The existing concrete receipt supplies its exact static fields. -/
def of_builtin (profile : CallablePreparedMethodRuntimeMeaning.Profile compiled values ambient sourceBody dictionary
    administrative registry faults) :
    ProfileFor compiled values ambient sourceBody dictionary administrative registry faults profile.expressionSyntax
      (fun context => CompatibleExpressionBuiltinRuntime.Certificate profile.readFuel values sourceBody.source context
        named.specialized.function.solvedRequirements (diagnostics.reasonAt named.signature.key))
      (fun context => CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)
      .reachable :=
  { sameSource := profile.sameSource, parameters := profile.parameters, sourceFrame := profile.sourceFrame
    context := profile.context, types := profile.types, extended := profile.extended, body := profile.body.toKernel
    definitions := profile.definitions, registered := profile.registered, parameterType := profile.parameterType }

variable {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : ProfileFor compiled values ambient sourceBody dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)

include profile extension faithful observations functionTypes escaped extend runtimeOf in
/-- Reflect this actual compiled hook. The bounded expression interface is
internal to the enclosing mutual proof; it is not a whole-program premise. -/
theorem ProfileFor.reflects_sized {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (expressions : ∀ context, validity context → RecursiveNamedBoundedContracts.Below size
      (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context dictionary sourceBody.source
        (certificates context) faults (protectedEntry named sourceBody (methodFunction compiled sourceBody dictionary)
          headers locations capturePrefix (callerPrefix + 1))))
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (compiled.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize (methodFunction compiled sourceBody dictionary)
        profile.context environment bound outcome after ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have acceptedPrefix : SourceCoreSourceCells.bindParameters
      (CallableIndexedNamedGeneration.allocator prepared named) sourceBody.source [] named.inputs
      named.signature.resultType SourceCoreFunctions.argumentProjection compiled.body = .ok compiled.parameterCode := by
    rw [profile.sameSource]
    exact compiled.parametersCompiled
  exact reflects_hook_sized (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
    (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
    (functions := functions) (extension := extension) (program := program)
    (onError := fun error => .sourceAllocation (reprStr error)) (kernel := profile.body) (escapedFault := escaped)
    (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
    (faithful := faithful) (functionLeaves := observations) (functionTypes := functionTypes)
    (acceptedPrefix := acceptedPrefix) (definitions := profile.definitions) (registered := profile.registered)
    (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
    (heaps := heaps) (initialLocals := installed.locals)
    (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
    (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
    (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
    (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller)
    (snapshots := installed.snapshots) (sourceFrame := profile.sourceFrame) (sameSource := profile.sameSource)
    (initial := initial) (sameFrame := sameFrame) (extend := extend) (runtimeOf := runtimeOf) expressions completed

end Compiled
end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodCatalogHookMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
/-! Static profiles retain the actual cached method, source-selected dictionary,
ordered parameters and accepted body callback. The compiler extractor is used
once at that same source and native body. Its own diagnostic receipt supplies
the sites; no expression or body execution law is stored in a profile. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallablePreparedMethodSelection CallableCoercionMethodInstantiation
open CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogHookMeaning

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ item, action = .ok item ∧ next item = .ok value := by
  cases action with
  | error error => cases accepted
  | ok item => exact ⟨item, rfl, accepted⟩

/-- The real retained method's declared callable type agrees with its raw input
binders before and after structural substitution. No packed arity is inverted. -/
theorem callable_shape {program : CheckedProgram} {method : ExecutableImplMethods.CheckedMethod}
    (receipt : CallableCoercionBodyProvenance.Certificate program method)
    (wellFormed : ProgramWellFormed (Program.ofChecked program)) :
    method.specialized.function.type = .function
      (TypeSystem.Ty.productMany (method.specialized.function.typedBody.inputs.map (fun b => b.scheme.body)))
      method.specialized.function.inferredBodyType := by
  have valid := wellFormed.methods_valid (MethodDefinition.ofChecked receipt.retained)
    (List.mem_map.mpr ⟨receipt.retained, receipt.retainedMember, rfl⟩)
  cases valid with
  | intro _ _ _ _ _ _ _ _ _ body =>
    cases body with
    | intro _ _ _ _ shape result _ _ _ extended _ _ _ _ _ _ =>
      have inputs := Dynamic.MonoBindersExtend.bodyTypes_eq extended
      change receipt.retained.checked.typedBody.inputs.map (fun b => b.scheme.body) = _ at inputs
      have genericShape : receipt.retained.checked.type = .function
          (TypeSystem.Ty.productMany (receipt.retained.checked.typedBody.inputs.map (fun b => b.scheme.body)))
          receipt.retained.checked.inferredBodyType := by
        rw [inputs]
        exact shape.trans (congrArg (TypeSystem.Ty.function _) result.symm)
      rw [receipt.result.2, genericShape]
      simp only [TypeSystem.ParameterSubstitution.apply]
      rw [← receipt.result.1, StructuralSubstitution.apply_productMany, receipt.inputs]
      simp only [List.map_map, Function.comp_def, StructuralSubstitution.applyBinder, StructuralSubstitution.applyScheme]

private theorem project_productMany {catalog : SourceCoreCompatibleCatalog.Catalog}
    {types : List TypeSystem.Ty} {native : List Core.Ty}
    (projected : types.mapM catalog.project = .ok native) :
    catalog.project (TypeSystem.Ty.productMany types) = .ok (SourceCoreCompatibleCatalog.packTypes native) := by
  induction types generalizing native with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
    subst native
    rfl
  | cons head tail ih =>
    rw [List.mapM_cons] at projected
    obtain ⟨first, firstProjected, projected⟩ := bind_ok projected
    obtain ⟨rest, restProjected, projected⟩ := bind_ok projected
    cases projected
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at restProjected
      subst rest
      exact firstProjected
    | cons next suffix =>
      have remaining := ih restProjected
      rw [List.mapM_cons] at restProjected
      obtain ⟨nextNative, _, restProjected⟩ := bind_ok restProjected
      obtain ⟨suffixNative, _, restProjected⟩ := bind_ok restProjected
      cases restProjected
      change (do pure (Ty.product (← catalog.project head)
        (← catalog.project (TypeSystem.Ty.productMany (next :: suffix))))) = _
      rw [firstProjected, remaining]
      rfl

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {method : ExecutableImplMethods.CheckedMethod}
  (cached : Cached compiled method.specialized)

theorem parameters : (bodyInstance compiled.sourceProgram method).source.inputs = cached.named.inputs.map Prod.fst := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have fields := SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted
  rw [← fields.1, cached.same] at fields
  exact fields.2.1.symm

theorem parameter_pack
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    cached.named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have shape := callable_shape receipt wellFormed
  have inputs := parameters cached
  change method.specialized.function.typedBody.inputs = _ at inputs
  rw [inputs] at shape
  have actualShape : row.function.type = .function
      (TypeSystem.Ty.productMany (cached.named.inputs.map (fun b => b.1.scheme.body)))
      row.function.inferredBodyType := by
    rw [← same, cached.same]
    simpa only [List.map_map, Function.comp_def] using shape
  have projected := CompatibleExpressionReads.projectType_of_accepted
    (RecursiveNamedHeaderParameterProjections.prepared_parameter accepted actualShape)
  have vector := project_productMany
    (RecursiveNamedPreparedParameterProjections.cached_projected compiled cached.selected)
  exact Except.ok.inj (projected.symm.trans vector)

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

private theorem prepared_outputs {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {specialized : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation specialized = .ok named) :
    named.signature.key = specialized.key ∧
      representation.expressions.projectType (.declaration specialized.key.declaration)
        specialized.function.inferredBodyType = .ok named.signature.resultType := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (specialized.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : specialized.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ specialized.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨parameterType, _, accepted⟩ := bind_ok accepted
      obtain ⟨resultType, projected, accepted⟩ := bind_ok accepted
      obtain ⟨inputs, _, accepted⟩ := bind_ok accepted
      cases accepted
      have resultEq : result = specialized.function.inferredBodyType := Classical.byContradiction mismatch
      exact ⟨rfl, by simpa only [resultEq] using mapError_ok projected⟩


theorem result_projection : compiled.compatible.checked.catalog.project
    (bodyInstance compiled.sourceProgram method).resultType = .ok cached.named.signature.resultType := by
  obtain ⟨row, _, accepted⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled cached.selected
  have same := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs accepted).1
  have projected := CompatibleExpressionReads.projectType_of_accepted (prepared_outputs accepted).2
  rw [← same, cached.same] at projected
  exact projected


section Static
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)

abbrev policy := CompatibleNamedBody.bodyPolicy
  ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
  prepared.base.sourceProgram prepared.base.sourceProgram.signatures prepared.base.locals compilation.parents
  compilation.own.assignments diagnostics (CallableIndexedNamedGeneration.context prepared named) prepared.base.callableContext

abbrev scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))

/-- Actual source attribution and full runtime validity at the real parameter context. -/
structure SourceAt (values : SourceCoreCompatibleValues.Context)
    (sourceBody : Dynamic.BodyInstance) (dictionary : Dynamic.EvidenceEnvironment) where
  sameSource : sourceBody.source = CallableIndexedNamedGeneration.source named
  parameters : sourceBody.source.inputs = named.inputs.map Prod.fst
  frame : CallableCoercionMethodFrame.Frame sourceBody (methodFunction compilation sourceBody dictionary)
  context : SourceSemantics.Context
  types : List TypeSystem.Ty
  extended : MonoBindersExtend sourceBody.source.owner sourceBody.context sourceBody.source.inputs types context
  valid : CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary
  closed : context.typeVariables = []
  residual : context.residualTypeVariables = true
  signatures : context.signatures = values.checked.signatures
  projection : values.checked.catalog.project sourceBody.resultType = .ok named.signature.resultType
  parameterType : named.signature.parameterType = SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd)
  unique : NodeOccurrencesUnique sourceBody.source

variable {values : SourceCoreCompatibleValues.Context} {sourceBody : Dynamic.BodyInstance}
  {dictionary : Dynamic.EvidenceEnvironment}

/-- The accepted body action is the same actual policy, source and statement vector. -/
theorem SourceAt.accepted (source : SourceAt compilation values sourceBody dictionary) :
    SourceCoreLoops.lowerStatementsWithPolicy (policy compilation) prepared.fuel sourceBody.source (scope (named := named))
      compilation.statements named.signature.resultType (diagnostics.reasonAt named.signature.key)
      compilation.own.fellThroughReason compilation.own.table.escapedReason = .ok compilation.body := by
  rw [source.sameSource]
  exact CallableCoercionMethodBody.loops_accepted compilation

private theorem reversed_scope (bindings : List (TypedBinder × Core.Ty)) (scope : SourceCoreLocalCell.Scope) :
    bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih => simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append,
      List.map_cons, List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

theorem SourceAt.declarations (source : SourceAt compilation values sourceBody dictionary) :
    CompatibleExpressionReads.ScopeDeclarations sourceBody.source (scope (named := named)) source.context := by
  have members : ∀ binding, binding ∈ named.inputs →
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders sourceBody.source := by
    intro binding member
    apply List.mem_append_left
    rw [source.parameters]
    exact List.mem_map.mpr ⟨binding, member, rfl⟩
  have extended := source.extended
  rw [source.parameters] at extended
  have initial : CompatibleExpressionReads.ScopeDeclarations sourceBody.source [] sourceBody.context := by
    intro _ _ _ _ selected _
    cases selected
  have final := RecursiveNamedHeaderScopeDeclarations.parameters members extended initial
  simpa only [reversed_scope, List.append_nil, scope] using final

end Static

/-- Independent whole-program validity and this exact source selection create
runtime context validity; the actual cache supplies ordered parameters and projections. -/
theorem source_at {values : SourceCoreCompatibleValues.Context}
    (sameChecked : values.checked = compiled.compatible.checked)
    (receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {context : SourceSemantics.Context} {callerEvidence dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {requirements : List RequirementId}
    (selected : Dynamic.OperatorMethodSelected (Program.ofChecked compiled.sourceProgram) context callerEvidence
      traitName methodName requirements (bodyInstance compiled.sourceProgram method) dictionary)
    (unique : NodeOccurrencesUnique (bodyInstance compiled.sourceProgram method).source)
    (signatures : compiled.sourceProgram.signatures = values.checked.signatures) :
    Nonempty (SourceAt cached.compilation values (bodyInstance compiled.sourceProgram method) dictionary) := by
  obtain ⟨types, lexical, facts, typed, valid⟩ := selected_typed selected wellFormed
  have fields := RecursiveNamedInitialContextValidity.mono_fields typed.typing.inputs_extend
  refine ⟨⟨?_, parameters cached, cached.frame selected, lexical, types, typed.typing.inputs_extend,
    ?_, fields.typeVariables.trans typed.type_variables_empty,
    fields.residualTypeVariables.trans typed.residual_type_variables_open,
    fields.signatures.trans (typed.signatures_eq.trans signatures), ?_, parameter_pack cached receipt wellFormed, unique⟩⟩
  · simp only [CallableIndexedNamedGeneration.source, cached.same, bodyInstance]
  · change CompatibleRuntimeContextValidity.Valid method.specialized.function.solvedRequirements lexical dictionary at valid
    simpa only [cached.same] using valid
  · rw [sameChecked]
    exact result_projection cached


/-- The exact cached lambda fixes this compilation's native body type. -/
theorem cached_body_native
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts} (member : entry ∈ compiled.indexed.entries) :
    HasType (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
      cached.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
      .cell compiled.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      cached.compilation.body (LanguageResult.resultType cached.named.signature.resultType) compiled.indexed.layouts.definitions := by
  have typed := CallableIndexedCachedNativeTyping.prepared_native_closure compiled.indexedPrepared member cached.cached
    (CallableIndexedPreparedInventories.cached_global_at compiled cached.selected)
  rw [cached.compilation.emitted] at typed
  cases typed with
  | lambda _ _ body =>
    simpa only [scope, List.append_assoc, List.cons_append] using CallableIndexedParameterNativeInversion.body_native cached.compilation body

/-- Only the used native prefix must agree. Unused administrative suffixes stay arbitrary. -/
theorem canonical_native {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts} (member : entry ∈ compiled.indexed.entries)
    {bound : Nat} {administrative : Core.Context}
    (support : NativeExpressionContextSupport.supported cached.compilation.body bound = true)
    (agrees : NativeExpressionContextSupport.Agrees bound
      (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
        cached.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
        .cell compiled.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
        SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative)) :
    HasType (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
      SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative)
      cached.compilation.body (LanguageResult.resultType cached.named.signature.resultType) ambient.definitions := by
  have typed := NativeExpressionContextSupport.typing (cached_body_native cached member) support agrees
  rwa [definitions] at typed

section Extract
variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code}
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  (source : SourceAt compilation values sourceBody dictionary)
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {administrative : Core.Context} {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- Admission of the reached static children in this actual callback.
The source context, projections, parameters and body acceptance come from SourceAt. -/
structure Inputs (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word
  invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy sourceBody.source invalidOperand
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess (policy compilation) matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = ambient.definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
    (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error))))
  matchLedger : matchCompilation.solvedRequirements = named.specialized.function.solvedRequirements
  matchChildStatic : GenericImperativeMatch.MatchChildStatic matchCompilation sourceBody.source
    certificates
    ambient.definitions administrative
  readPolicy : (policy compilation).readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    (policy compilation).lowerBinder sourceBody.source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked sourceBody.source scope binder
  allocationPolicy : (policy compilation).sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator prepared.ancestry.layout.frame prepared.base.globals.length
    (prepared.layouts.allocatorAt named.signature.key [] (fun error => .sourceAllocation (reprStr error))))
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations sourceBody.source scope sourceContext → expressionSyntax id →
    sourceBody.source.lookupExpression? id = some node → ExpressionHasType sourceBody.source sourceContext id node.type →
    (policy compilation).lowerExpression fuel sourceBody.source scope id (diagnostics.reasonAt named.signature.key) = .ok lowered →
    certificates sourceContext scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy (policy compilation) values invalidProjection invalidOperand missingDefault
  unaryPolicy : CompatibleBitNotStatements.Policy (policy compilation) values invalidProjection invalidUnary missingDefault
  assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = true →
    sourceContext.signatures = values.checked.signatures →
    CompatibleExpressionReads.ScopeDeclarations sourceBody.source scope sourceContext →
    expressionSyntax id → ∀ node, sourceBody.source.lookupExpression? id = some node →
    ExpressionHasType sourceBody.source sourceContext id node.type →
    (policy compilation).lowerExpression fuel sourceBody.source scope id (diagnostics.reasonAt named.signature.key) = .ok lowered →
      certificates sourceContext scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) ambient.definitions
  syntaxTree : GenericImperativeMatch.Syntax sourceBody.source expressionSyntax source.context
    (.statements true compilation.statements) sourceBody.resultType


/-- This extraction is indexed by the actual compiled body and actual dictionary.
Only its own diagnostics can materialize its same Tree and sites. -/
structure Receipt (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (diagnosticPolicy : AssignmentDiagnosticPolicy) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) where
  flow : Expr
  extracted : GenericImperativeMatch.ExtractionFor diagnosticPolicy prepared.layouts named.signature.key []
    prepared.ancestry.layout.frame prepared.base.globals.length (fun error => .sourceAllocation (reprStr error))
    values sourceBody.source expressionSyntax certificates ambient.definitions administrative
    named.specialized.function.solvedRequirements source.context (scope (named := named))
    (.statements true compilation.statements) sourceBody.resultType named.signature.resultType flow
  emitted : compilation.body = CompatibleStatements.finish named.signature.resultType flow
    compilation.own.fellThroughReason compilation.own.table.escapedReason

/-- The common extractor traverses the actual body once. No semantic callback is needed. -/
theorem extract (inputs : Inputs source (ambient := ambient) certificates tracked diagnosticPolicy expressionSyntax administrative)
    (typed : HasType (SourceCoreLocalCell.coreContext (scope (named := named)) ++ administrative)
      compilation.body (LanguageResult.resultType named.signature.resultType) ambient.definitions) :
    Nonempty (Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax administrative) := by
  obtain ⟨flow, generated, extracted, emitted⟩ := GenericImperativeMatch.extraction_of_typed_body_with_lowering true diagnosticPolicy
    inputs.factory inputs.matchPolicy inputs.matchValues inputs.matchDefinitions inputs.matchAllocator inputs.matchChildStatic
    inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy inputs.expressions inputs.assignments inputs.unaryPolicy
    source.unique inputs.assignmentExpressions inputs.syntaxTree source.closed source.residual source.signatures
    (source.declarations compilation) source.projection (source.accepted compilation) typed
  rw [inputs.matchLedger] at extracted
  exact ⟨⟨flow, extracted, emitted⟩⟩

/-- The good returned receipt constructs the existing same-dictionary profile. -/
def Receipt.profile
    (receipt : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative))
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (definitions : prepared.layouts.definitions = ambient.definitions)
    (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (interpreted : receipt.extracted.diagnostics registry faults) :
    ProfileFor compilation values ambient sourceBody dictionary administrative registry faults
      expressionSyntax certificates
      (fun context => CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)
      diagnosticPolicy := by
  have sites : GenericImperativeMatch.Tree.CatalogSites diagnosticPolicy registry faults receipt.extracted.tree := by
    obtain ⟨errors, ledgers⟩ := receipt.extracted.materialize registry faults interpreted
    exact RecursiveNamedCatalogRuntimeProfileFactory.catalog_sites catalog ledgers source.valid.ledger source.signatures
  exact {
    sameSource := source.sameSource
    parameters := source.parameters
    sourceFrame := source.frame
    context := source.context
    types := source.types
    extended := source.extended
    body := {
      flow := receipt.flow
      tree := receipt.extracted.tree
      sites := sites
      initialValid := source.valid
      projection := source.projection
      unique := source.unique
      emitted := receipt.emitted }
    definitions := definitions
    registered := registered
    parameterType := source.parameterType }

end Extract


/-- Actual cached native typing supplies the only whole-body typing premise.
The remaining inputs concern syntax, used slots and reached static children. -/
theorem extract_cached {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {dictionary : Dynamic.EvidenceEnvironment}
    (source : SourceAt cached.compilation values (bodyInstance compiled.sourceProgram method) dictionary)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy} {administrative : Core.Context}
    (inputs : Inputs source (ambient := ambient) certificates tracked diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative))
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts} (member : entry ∈ compiled.indexed.entries)
    {bound : Nat} (support : NativeExpressionContextSupport.supported cached.compilation.body bound = true)
    (agrees : NativeExpressionContextSupport.Agrees bound
      (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
        cached.named.signature.parameterType :: compiled.indexed.base.globals.map (·.referenceType) ++
        .cell compiled.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      (SourceCoreLocalCell.coreContext (scope (named := cached.named)) ++
        SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative)) :
    Nonempty (Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative)) :=
  extract source inputs (canonical_native cached definitions member support agrees)

/-- Interpretation belongs to this exact returned receipt, not every possible
receipt. Witness selection stays inside the proposition. -/
theorem profile_of_interpreted {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {dictionary : Dynamic.EvidenceEnvironment}
    (source : SourceAt cached.compilation values (bodyInstance compiled.sourceProgram method) dictionary)
    {expressionSyntax : ExpressionId → Prop}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {diagnosticPolicy : AssignmentDiagnosticPolicy} {administrative : Core.Context}
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
    (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (good : ∃ receipt : Receipt source (ambient := ambient) certificates diagnosticPolicy expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (cached.named.inputs.map Prod.snd) :: administrative),
      receipt.extracted.diagnostics registry faults) :
    Nonempty (ProfileFor cached.compilation values ambient (bodyInstance compiled.sourceProgram method) dictionary
      administrative registry faults expressionSyntax certificates
      (fun context => CompatibleRuntimeContextValidity.Valid cached.named.specialized.function.solvedRequirements context dictionary)
      diagnosticPolicy) := by
  obtain ⟨receipt, interpreted⟩ := good
  exact ⟨receipt.profile source catalog definitions registered interpreted⟩

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodRuntimeProfileFactory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodOriginMeaning
/-! Actual method profiles enter the neutral body family with their own full
source dictionary and protected method entry. Original hook completion supplies
the strict native child. The family induction hypothesis is consumed once;
restoration reuses the actual prefix and caller receipts. Source preservation
is exposed only at an already reached entry, not for the whole source hook. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodOriginMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : ProfileFor compiled values ambient sourceBody dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)


/-- Every field comes from this actual compiled profile and dictionary. The
protected entry retains method attribution separately from its named history. -/
def ProfileFor.origin : CallableRuntimeBodyOrigins.Origin values ambient registry faults where
  layouts := prepared.layouts
  owner := named.signature.key
  active := []
  frameLayout := prepared.ancestry.layout.frame
  globals := prepared.base.globals.length
  onError := fun error => .sourceAllocation (reprStr error)
  function := methodFunction compiled sourceBody dictionary
  expressionSyntax := expressionSyntax
  certificates := certificates
  validity := validity
  diagnosticPolicy := diagnosticPolicy
  administrative := SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative
  context := profile.context
  scope := named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))
  output := named.signature.resultType
  code := compiled.body
  fellThrough := compiled.own.fellThroughReason
  escaped := compiled.own.table.escapedReason
  solved := named.specialized.function.solvedRequirements
  protectedEntry := protectedEntry named sourceBody (methodFunction compiled sourceBody dictionary)
    headers locations capturePrefix (callerPrefix + 1)
  body := profile.body
  definitions := profile.definitions
  registered := profile.registered
  escapedFault := escaped
  transport := CallablePreparedMethodCatalogEntries.transport
  binders := CallablePreparedMethodCatalogEntries.binds
  extend := extend
  runtimeOf := runtimeOf

/-- The source budget stays the original budget. The caller supplies a reached
entry; no unsized parameter entry or source hook execution is reconstructed. -/
theorem ProfileFor.preserves_reached_of_below (budget child : Nat) (strict : child < budget)
    (below : RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyOrigins.PreservesAt functions program
        (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf))) :
    CallableRuntimeBodyOrigins.PreservesAt functions program
      (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf) child :=
  below child strict

section Prefix
variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {arguments : List Dynamic.Value} {payloads : List Value} {actualContext : Core.Context}
  {canonical actual : Environment} {ξ : Renaming} {prefixSize : Nat} {value : Value} {bodyStore : Store}
  {location : Location} {next : NativeFrame}
  (reached : Prefix prepared.ancestry.layout.frame prepared.base.globals.length location next values functions registry
    (methodFunction compiled sourceBody dictionary) profile.context named.inputs arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world administrative actualContext
    actual ξ compiled.parameterCode compiled.body prefixSize value bodyStore)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = named.inputs.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues payloads :: canonical)
  {originId : Word} {metadata : MetadataState}
  (owned : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId)
  (history : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next (.named originId) (some metadata))

/-- The original reached prefix supplies every dynamic field; the full spine
is used by the existing catalog constructor at the same physical frame. -/
def entry_of_prefix : CallableRuntimeBodyOrigins.Entry
    (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf) functions where
  mapping := reached.mapping
  world := reached.world
  environment := reached.environment
  canonical := reached.canonical
  actual := reached.actualBody
  heap := reached.heap
  store := reached.store
  embedding := reached.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext named.inputs actualContext
  frameLocation := location
  native := next
  environments := reached.environments
  heaps := reached.heaps
  locals := reached.locals
  lookups := reached.lookups
  actualTyped := reached.actualTyped
  reference := reached.reference
  read := reached.read
  unmapped := reached.unmapped
  installed := ⟨source_entry reached initial sameFrame length spine owned history profile.sourceFrame profile.sameSource⟩

end Prefix

theorem ProfileFor.reflects_hook_of_below (budget : Nat) {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store finalStore : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    {size : Nat} {value : Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (within : size ≤ budget)
    (below : RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyOrigins.ReflectsAt functions program
        (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf)))
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: installed.captured) store
      (compiled.output.rename installed.embedding.lift) value finalStore) :
    ∃ sourceSize environment bound outcome after finalMap finalWorld,
      Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace program sourceSize (methodFunction compiled sourceBody dictionary)
        profile.context environment bound outcome after ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have acceptedPrefix : SourceCoreSourceCells.bindParameters
      (CallableIndexedNamedGeneration.allocator prepared named) sourceBody.source [] named.inputs
      named.signature.resultType SourceCoreFunctions.argumentProjection compiled.body = .ok compiled.parameterCode := by
    rw [profile.sameSource]
    exact compiled.parametersCompiled
  obtain ⟨originId, index, metadata, bodyStore, prefixSize, owned, history, prefixStrict, finalEq,
    reached, added, length, spine⟩ :=
    hook_prefix_with_spine (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
      (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
      (functions := functions) (onError := fun error => .sourceAllocation (reprStr error))
      (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
      (acceptedPrefix := acceptedPrefix) (definitions := profile.definitions) (registered := profile.registered)
      (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
      (heaps := heaps) (initialLocals := installed.locals)
      (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
      (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
      (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller) completed
  have strict : reached.childSize < budget := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt reached.bounded prefixStrict) within
  let actualEntry := entry_of_prefix compiled profile functions escaped extend runtimeOf
    reached initial sameFrame length spine owned history
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds,
    frame, sourceMetadata, reachedExit, retained⟩ := below reached.childSize strict actualEntry reached.completed
  obtain ⟨restoredHeaps, restoredCatalog, restoredFrame, restoredCaller⟩ :=
    restore_catalog reached initial sameFrame installed.caller profile.registered finalHeaps maps worlds frame sourceMetadata
  have source := profile.sourceFrame.body_of_trace profile.extended reached.allocation trace.sound
  subst finalStore
  exact ⟨sourceSize, reached.environment, reached.heap, outcome, after, finalMap, finalWorld,
    reached.allocation, trace, source, related, restoredHeaps, reached.maps.trans maps, reached.worlds.trans worlds,
    restoredFrame, reached.metadata.trans sourceMetadata, reachedExit, restoredCatalog, restoredCaller,
    installed.snapshots.transport restoredFrame⟩

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodOriginMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSourceHookMeaning
/-! Source method body execution enters the actual compiled hook through its
retained parameter spine. Catalog authority is constructed before body
completion from real installation and allocation effects. The original source
body grade and its family hypothesis remain explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSourceHookMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof CompatiblePayload
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallablePreparedMethodRuntimeMeaning CallablePreparedMethodCatalogEntries
open CallablePreparedMethodCatalogHookMeaning CallablePreparedMethodOriginMeaning
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation prepared named diagnostics code)
  {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {sourceBody : Dynamic.BodyInstance} {dictionary : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {validity : SourceSemantics.Context → Prop} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : ProfileFor compiled values ambient sourceBody dictionary administrative registry faults
    expressionSyntax certificates validity diagnosticPolicy)
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {program : Program}
  {headers : RecursiveNamedCatalog.Inventory prepared.ancestry values ambient.definitions program}
  {locations : RecursiveNamedCatalog.Locations (prepared := prepared.ancestry) (values := values) (ambient := ambient) (program := program)}
  {capturePrefix callerPrefix : Nat}
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (escaped : faults .controlEscapedFunction compiled.own.table.escapedReason)
  (extend : ∀ {context next binder}, validity context → BinderExtends sourceBody.source.owner context binder next → validity next)
  (runtimeOf : ∀ {context}, validity context →
    CompatibleRuntimeContextValidity.Valid named.specialized.function.solvedRequirements context dictionary)


section Parameters
variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {arguments : List Dynamic.Value} {payloads : List Value} {actualContext : Core.Context}
  {canonical actual : Environment} {ξ : Renaming}
  {location : Location} {next : NativeFrame}
  (reached : TypedMixedNamedParameters.Entry prepared.ancestry.layout.frame prepared.base.globals.length location next values functions registry
    (methodFunction compiled sourceBody dictionary) profile.context named.inputs arguments before
    (store.set location (encode prepared.ancestry.layout.frame next)) mapping world administrative actualContext
    actual ξ compiled.parameterCode compiled.body)
  (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store canonical)
  (sameFrame : initial.authority.frameLocation = location)
  {added : Environment} (length : added.length = named.inputs.length)
  (spine : reached.canonical = added ++ DataPatternValues.packValues payloads :: canonical)
  {originId : Word} {metadata : MetadataState}
  (owned : prepared.ancestry.graph.inputs.callable.table.idAt? (.named named.signature.key) = some originId)
  (history : Carries prepared.ancestry.graph.inputs prepared.ancestry.graph.table next (.named originId) (some metadata))

/-- The accepted parameter entry supplies every field before body evaluation.
Its actual installation, complete history and ordered spine construct the same protected origin entry. -/
def entry_of_parameters : CallableRuntimeBodyOrigins.Entry
    (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
      (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf) functions where
  mapping := reached.mapping
  world := reached.world
  environment := reached.environment
  canonical := reached.canonical
  actual := reached.actualBody
  heap := reached.heap
  store := reached.store
  embedding := reached.embedding
  actualContext := CallableIndexedParameterTyped.prefixContext named.inputs actualContext
  frameLocation := location
  native := next
  environments := reached.environments
  heaps := reached.heaps
  locals := reached.locals
  lookups := reached.lookups
  actualTyped := reached.actualTyped
  reference := reached.reference
  read := reached.read
  unmapped := reached.unmapped
  installed := ⟨source_entry_of_effects initial sameFrame reached.maps reached.worlds reached.frame reached.metadata
    length spine reached.reference owned history profile.sourceFrame profile.sameSource⟩

end Parameters

/-- The original source body grade executes the real compiled hook. The
neutral family hypothesis is consumed once at the actual parameter state;
the shared envelope restores the full caller catalog and snapshots. -/
theorem ProfileFor.preserves_hook_of_below (budget child : Nat) (strict : child < budget)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap}
    {store : Store} {callerEnvironment : Environment} {arguments : List Dynamic.Value} {payloads : List Value}
    (installed : Installed compiled (sourceBody := sourceBody) (administrative := administrative) functions mapping world before store callerEnvironment)
    (initial : RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] mapping world before store installed.canonical)
    (sameFrame : initial.authority.frameLocation = installed.frameLocation)
    (represented : Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      mapping world named.inputs arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (below : RecursiveNamedBoundedContracts.Below budget
      (CallableRuntimeBodyOrigins.PreservesAt functions program
        (ProfileFor.origin (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          (callerPrefix := callerPrefix) compiled profile escaped extend runtimeOf)))
    {environment : Dynamic.Environment} {bound after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (allocated : Dynamic.BindersAllocate [] before sourceBody.source.inputs arguments environment bound)
    (trace : RecursiveNamedCallBounds.BodyTrace program child (methodFunction compiled sourceBody dictionary)
      profile.context environment bound outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues payloads :: installed.captured) store
        (compiled.output.rename installed.embedding.lift) value finalStore ∧
      CallableCoercionMethodFrame.BodyOutcome program sourceBody dictionary before arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld sourceBody.resultType named.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld
        (SourceCoreCompatibleCatalog.packTypes (named.inputs.map Prod.snd) :: administrative) program
        (methodFunction compiled sourceBody dictionary) profile.context
        (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) environment bound after outcome ∧
      Nonempty (RecursiveNamedCatalog.Entry headers locations capturePrefix callerPrefix [] finalMap finalWorld after finalStore installed.canonical) ∧
      CellState prepared.ancestry.graph.inputs prepared.ancestry.graph.table prepared.ancestry.layout.frame
        installed.frameLocation installed.current installed.currentGhost finalStore ∧
      CallableIndexedSnapshots.All prepared.ancestry.graph.inputs prepared.ancestry.graph.table
        prepared.ancestry.layout.frame finalMap finalStore installed.records := by
  have acceptedPrefix : SourceCoreSourceCells.bindParameters
      (CallableIndexedNamedGeneration.allocator prepared named) sourceBody.source [] named.inputs
      named.signature.resultType SourceCoreFunctions.argumentProjection compiled.body = .ok compiled.parameterCode := by
    rw [profile.sameSource]
    exact compiled.parametersCompiled
  obtain ⟨originId, index, metadata, value, finalStore, finalMap, finalWorld, owned, history,
    evaluated, related, finalHeaps, maps, worlds, frame, sourceMetadata, caller, snapshots, reachedExit⟩ :=
    BuiltinNamedCalls.hook_preserves_with_spine
      (prepared := prepared.ancestry) (function := methodFunction compiled sourceBody dictionary)
      (layouts := prepared.layouts) (owner := named.signature.key) (active := [])
      (functions := functions) (program := program) (onError := fun error => .sourceAllocation (reprStr error))
      (parameters := profile.parameters) (inputs := profile.parameters) (extended := profile.extended)
      (acceptedPrefix := acceptedPrefix) (definitions := profile.definitions) (registered := profile.registered)
      (acceptedHook := compiled.hook) (represented := represented) (environments := installed.environments)
      (heaps := heaps) (initialLocals := installed.locals)
      (actualLayout := ReadOnly.EnvironmentsAgree.lift installed.captureLayout (DataPatternValues.packValues payloads))
      (actualTyped := RuntimeEnvironmentHasTypes.cons (CallableIndexedParameters.Arguments.pack_typed represented) installed.captureTyped)
      (canonicalReference := installed.canonicalReference) (actualReference := installed.capturedReference)
      (unmapped := installed.unmapped) (typed := installed.frameTyped) (caller := installed.caller) (snapshots := installed.snapshots)
      (RecursiveNamedCallBounds.BodyTrace program child (methodFunction compiled sourceBody dictionary) profile.context)
      (by
        intro originId index metadata owned history prefixContext prefixActual embedding entry added length spine outcome after sourceTrace
        let actualEntry := entry_of_parameters compiled profile functions escaped extend runtimeOf
          entry initial sameFrame length spine owned history
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related, finalHeaps, maps, worlds,
          frame, sourceMetadata, reachedExit, retained⟩ := below child strict actualEntry sourceTrace
        exact ⟨value, finalStore, finalMap, finalWorld, entry.agreement.wrap evaluated, related, finalHeaps,
          entry.maps.trans maps, entry.worlds.trans worlds, entry.frame.trans frame, entry.metadata.trans sourceMetadata, reachedExit⟩)
      allocated trace
  have source := profile.sourceFrame.body_of_trace profile.extended allocated trace.sound
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, source, related, finalHeaps,
    maps, worlds, frame, sourceMetadata, reachedExit, ⟨initial.extend maps worlds frame sourceMetadata⟩, caller, snapshots⟩

end Solcore.SourceSemantics.CoreLowering.CallablePreparedMethodSourceHookMeaning
end
