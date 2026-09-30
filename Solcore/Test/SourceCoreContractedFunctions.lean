import Solcore.SourceSemantics.CoreLowering.ContractedFunctionCalls

/-! Actual decorated lambda compilation and independent source formation.
A sealed descriptor is a static input. The real emitted wrapper and guards
preserve the actual capture environment, including an inserted integer slot.
No interpretation of rejected stage guards as old Dynamic faults is assumed. -/

set_option autoImplicit false
namespace Tests.SourceCoreContractedFunctions
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap FunctionCaptures

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"contracted_functions", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def id : ExpressionId := ⟨⟨owner, 0⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "contracted_functions.solc"⟩, 0, 1⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def program : Program := ⟨signatures, [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { callableContracts := true }
private def sourceType : TypeSystem.Ty := .function .unit .unit
private def functionType : Core.Ty := Core.CallableContract.functionType .unit .unit
private def node : ExpressionNode := { id, span, type := sourceType, form := .lambda [] .unit [] }
private def source : TypedSource := { owner, inputs := [], roots := [.expression id], nodes := [.expression node] }
private def context : SourceSemantics.Context := {
  SourceSemantics.Context.ofSignatures signatures with
  currentDeclaration := some owner, residualTypeVariables := true }
private def function : Dynamic.Closure := {
  parameters := [], resultType := .unit, body := [], source, captured := [], context, evidence := [] }
private def compilation : SourceCoreFunctions.Context := {
  plan := ⟨[], [], [], []⟩, owner := ⟨owner, []⟩, globals := [], administrativePrefix := 0
  solvedRequirements := [], internalReason := Core.Word.zero }
private def lowerBody : SourceCoreFunctions.BodyLowerer :=
  fun _ budget source scope statements result _ reason _ =>
    SourceCoreBasic.lowerStatements budget source scope statements result reason
private def bodyCertificate : FunctionCode.BodyCertificate := fun _ _ statements type code =>
  statements = [] ∧ type = .unit ∧ code = Core.LanguageResult.success .unit

private def policy {table : SourceCoreStageCodebook.Table}
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id [])) : SourceCoreFunctions.Policy := {
  readExpression := fun _ _ => pure (node, functionType)
  callables := {
    functionType := Core.CallableContract.functionType
    decorateCallable := fun _ _ _ _ _ _ raw => match raw with
      | .inRight .word value => pure (Core.LanguageResult.success (descriptor.wrap value))
      | _ => .error (.unsupportedExpression id node.form) } }
private def emitted {table : SourceCoreStageCodebook.Table}
    (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id [])) : SourceCoreBasic.LoweredExpr :=
  ⟨functionType, Core.LanguageResult.success (descriptor.wrap (Core.TaggedFunction.anonymous
    (.lambda .unit (Core.LanguageResult.resultType .unit) (Core.LanguageResult.success .unit))))⟩

variable {table : SourceCoreStageCodebook.Table}
  (descriptor : SourceCoreCallableContracts.Descriptor table (.lambda compilation.owner id []))

private theorem artifact_exists : Nonempty
    (DecoratedFunctionCode.LambdaCertificate bodyCertificate (policy descriptor) compilation source [] id node
      [] .unit [] functionType (emitted descriptor)) := by
  apply DecoratedFunctionCode.lambda_of_accepted (lowerBody := lowerBody) (fuel := 0)
    (policy := policy descriptor) (context := compilation) (source := source) (scope := []) (id := id) (node := node)
    (reasonAt := fun _ => Core.Word.zero) rfl rfl rfl rfl
  · intro budget bodyScope type code accepted
    simp only [lowerBody, SourceCoreBasic.lowerStatements] at accepted
    split at accepted
    · next same => cases accepted; exact ⟨rfl, same, rfl⟩
    · cases accepted
  · cbv

private noncomputable def artifact : DecoratedFunctionCode.LambdaCertificate bodyCertificate (policy descriptor)
    compilation source [] id node [] .unit [] functionType (emitted descriptor) := Classical.choice (artifact_exists descriptor)

private theorem parameter_type : (artifact descriptor).raw.parameterCore = .unit := by
  have selected := (artifact descriptor).raw.parameterProjection
  rw [← (artifact descriptor).raw.bundle] at selected
  exact Except.ok.inj selected.symm
private theorem result_type : (artifact descriptor).raw.resultCore = .unit :=
  Except.ok.inj (artifact descriptor).raw.resultProjection.symm

private theorem graph : OccurrenceGraphWellFormed source := by
  constructor
  · unfold NodeOccurrencesUnique nodeOccurrenceIds; decide
  · intro selected member
    simp only [source, List.mem_singleton] at member
    subst selected; rfl
  · intro root member
    simp only [source, List.mem_singleton] at member
    subst root; rfl
  · intro root member
    simpa [source, nodeIds, Node.id, node] using member
  · intro selected member child childMember
    simp only [source, List.mem_singleton] at member
    subst selected; cases childMember

private theorem frame : Dynamic.ClosureFrame program function := by
  have unique : RequirementIdsUnique context := by simp [RequirementIdsUnique, context, Context.ofSignatures]
  have covers : Dynamic.EvidenceEnvironment.Covers context [] := by
    constructor
    · intro goal evidence impossible; cases impossible
    · intro predicate impossible; cases impossible
  refine ⟨rfl, rfl, ?_, unique, covers⟩
  refine ⟨rfl, rfl, rfl, rfl, graph, ⟨unique, ?_⟩, ?_⟩
  · intro row evidence member; cases member
  · refine ⟨id, node, ⟨by change Node.expression node ∈ [Node.expression node]; exact List.mem_singleton_self _, rfl⟩, rfl, rfl, ?_⟩
    exact .lambda (by decide) (.nil _) (.nil _ _) ⟨rfl, rfl, .inr rfl⟩

private def canonical : Core.Environment := [.word Core.Word.zero]
private def actual : Core.Environment := [.integer 11, .word Core.Word.zero]
private def layout : Layout catalog [] [] [] function.captured actual where
  administrativeContext := [.word]
  canonical := canonical
  actualContext := [.integer, .word]
  embedding := Core.Renaming.insertion 0
  represented := .nil (.cons .word .nil)
  lookups := Core.ReadOnly.EnvironmentsAgree.insertion canonical 0 (.integer 11)
  types := Core.Renaming.insertion_respects_insertAt [.word] 0 .integer
  actualTyped := .cons .integer (.cons .word .nil)

private noncomputable def code : ContractedFunctionValues.Code catalog program bodyCertificate (policy descriptor)
    compilation table [] function [] [.word] where
  id := id
  node := node
  reportedType := functionType
  lowered := emitted descriptor
  artifact := artifact descriptor
  owner := rfl
  descriptor := descriptor
  decoration := fun _ => rfl
  frame := frame
  projection := by rw [parameter_type descriptor, result_type descriptor]; rfl
  outputTyped := by
    rw [parameter_type descriptor, result_type descriptor]
    exact .inRight .word (.pair (Core.TaggedFunction.anonymous_hasType (.lambda .unit (.sum .word .unit)
      (.inRight .word .unit))) .word)

private def generated : Core.Value := .pair (FunctionValues.value .unit .unit
  (Core.LanguageResult.success .unit) layout.embedding actual) (.word descriptor.id)

private theorem raw_body : (artifact descriptor).raw.rawBody = Core.LanguageResult.success .unit := by
  have binders := (artifact descriptor).raw.parametersTree.binders
  have noParameters : (artifact descriptor).raw.loweredParameters = [] := List.map_eq_nil_iff.mp binders
  simp only [FunctionCode.LambdaCertificate.rawBody, noParameters, SourceCoreFunctions.bindParameters,
    List.zipIdx_nil, List.foldr_nil, List.length_nil, (artifact descriptor).raw.bodyTree.2.2]
  simp only [Core.LanguageResult.success, Core.Expr.weakenAt]

example : Dynamic.ExpressionEvaluates program context [] source [] ⟨[]⟩ id (.closure function) ⟨[]⟩ ∧
    Core.Evaluates actual [] ((emitted descriptor).expression.rename layout.embedding)
      (.inRight .word (generated descriptor)) [] := by
  obtain ⟨sourceEval, coreEval, _⟩ := ContractedFunctionValues.formation_corresponds layout (code descriptor) ⟨[]⟩ [] rfl rfl
  refine ⟨sourceEval, ?_⟩
  change Core.Evaluates actual [] ((emitted descriptor).expression.rename layout.embedding)
    (.inRight .word (ContractedFunctionValues.value (artifact descriptor).raw.parameterCore
      (artifact descriptor).raw.resultCore (artifact descriptor).raw.rawBody layout.embedding actual descriptor.id)) [] at coreEval
  rw [raw_body descriptor, parameter_type descriptor, result_type descriptor] at coreEval
  exact coreEval

example (identities : Dynamic.Value → Core.Word → Prop) :
    DataEqualityValues.Observation catalog signatures identities functionType (.closure function) (generated descriptor) := by
  have observed := ContractedFunctionValues.Represents.observation
    (ContractedFunctionValues.Represents.closure layout (code descriptor)) signatures identities
  change DataEqualityValues.Observation catalog signatures identities
    (Core.CallableContract.functionType (artifact descriptor).raw.parameterCore (artifact descriptor).raw.resultCore)
    (.closure function) (ContractedFunctionValues.value (artifact descriptor).raw.parameterCore
      (artifact descriptor).raw.resultCore (artifact descriptor).raw.rawBody layout.embedding actual descriptor.id) at observed
  rw [raw_body descriptor, parameter_type descriptor, result_type descriptor] at observed
  exact observed

/-- Both gates accept, and the exact call prefix can be removed from every
completed evaluation without changing the actual captured body environment. -/
example : CoreProof.ContinuationAgreement actual []
    (Core.CallableContract.call [⟨descriptor.id, none, none⟩] Core.Word.zero .unit
      ((emitted descriptor).expression.rename layout.embedding) (Core.LanguageResult.success .unit))
    (.unit :: actual) [] (Core.LanguageResult.success .unit) := by
  apply ContractedFunctionCalls.accepted_call_agreement (contract := descriptor.id)
    (identity := .inLeft .word .unit) (parameter := .unit) (middle := []) (applied := [])
  · have evaluated := (ContractedFunctionValues.formation layout (code descriptor) []).1
    change Core.Evaluates actual [] ((emitted descriptor).expression.rename layout.embedding)
      (.inRight .word (ContractedFunctionValues.value (artifact descriptor).raw.parameterCore
        (artifact descriptor).raw.resultCore (artifact descriptor).raw.rawBody layout.embedding actual descriptor.id)) [] at evaluated
    rw [raw_body descriptor, parameter_type descriptor, result_type descriptor] at evaluated
    simpa only [ContractedFunctionValues.value, FunctionValues.value, Core.LanguageResult.success, Core.Expr.rename] using evaluated
  · simp [Core.CallableContract.decision, Core.CallableContract.Gate.reason]
  · simpa only [Core.LanguageResult.success, Core.Expr.weakenAt] using
      (Core.Evaluates.inRight (leftType := Core.Ty.word) Core.Evaluates.unit :
        Core.Evaluates _ [] (.inRight .word .unit) (.inRight .word .unit) [])
  · simp [Core.CallableContract.decision, Core.CallableContract.Gate.reason]

end Tests.SourceCoreContractedFunctions
