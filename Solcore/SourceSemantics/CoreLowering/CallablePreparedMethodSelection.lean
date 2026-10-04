import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodFrame
import Solcore.SourceSemantics.CoreLowering.CallableCoercionExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleRuntimeContextValidity
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections

/-! Actual operator selection retains the full synthetic method, ordered
source evidence, and the compiler's chosen plan row. It does not reinterpret
an implementation method as an ordinary program function. -/
set_option autoImplicit false
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
    {loaded : LoadedProgram} (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
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
theorem SourceReceipt.retained {loaded : LoadedProgram}
    (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok program)
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
    {loaded : LoadedProgram} (loadedAccepted : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
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
