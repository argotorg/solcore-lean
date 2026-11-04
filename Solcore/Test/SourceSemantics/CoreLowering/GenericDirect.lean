import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicWordResultMeaning
import Solcore.Test.SourceSemantics.CoreLowering.OperatorCalls
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicExecutionMeaning
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedFiniteNamedInventories
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryFrontdoor
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSimpleInputRegistry
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputRegistry
import Solcore.SourceSemantics.CoreLowering.CompatibleRegistryDiagnosticExtension
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedOutputPreservation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicActualRegistryNamedOutputPreservation

/-!
# Generic direct call tests

Generic direct calls through their closure family and public execution.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectResults
/-! Exact Bool output follows from the actual public encoder and the independent
Source/native result. No decoder success or Source value law is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Core GeneralHeap CompatiblePayload
open SourceCoreIndexedSession

private theorem encoded_bool_value {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {publicValue : SourceCorePublicValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    {value : Bool}
    (accepted : session.RawEncodedAt fuel registry .bool publicValue encoded)
    (payload : encoded.value = .bool value) : publicValue = .bool value := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases publicValue <;> try cases accepted
      case bool.refl =>
        exact congrArg SourceCorePublicValues.Value.bool (Core.Value.bool.inj payload)
      case constructed metadata values =>
        obtain ⟨_, _, _, _, _, _, _, _, same⟩ := accepted.constructed
        rw [same] at payload
        cases payload

theorem succeeded_bool_value {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {store : Core.Store} {completion : Completion artifact} {value : Bool}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation
      (.inRight .word (.bool value)) store completion)
    (requested : checkpoint.ResultTypeAt .bool) : completion.value = .bool value := by
  obtain ⟨_sourceType, encoded, accepted, payload⟩ := succeeded.reimports_payload requested rfl
  exact encoded_bool_value accepted payload

theorem represented_bool
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome}
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact} {value : Bool}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt .bool)
    (exported : completion.value = .bool value)
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world rawType .bool
      faults outcome native) : outcome = .value (.bool value) := by
  obtain ⟨payload, decoded, _⟩ := succeeded.reimports
  cases represented with
  | value related =>
    obtain ⟨actual, rfl, rfl⟩ := CompatibleExpressionPrimitives.bool_fields related
    have actualOutput := succeeded_bool_value succeeded requested
    have same := SourceCorePublicValues.Value.bool.inj (actualOutput.symm.trans exported)
    rw [same]
  | fault related =>
    simp only [LanguageResult.decode?, Option.some.injEq] at decoded
    cases decoded

/-- The fixture has exactly the two scalar public result profiles it executes. -/
inductive ScalarOutput where
  | word (value : Core.Word)
  | bool (value : Bool)

def ScalarOutput.sourceType : ScalarOutput → TypeSystem.Ty
  | .word _ => .word
  | .bool _ => .bool

def ScalarOutput.nativeType : ScalarOutput → Core.Ty
  | .word _ => .word
  | .bool _ => .bool

def ScalarOutput.source : ScalarOutput → Dynamic.Value
  | .word value => .word value
  | .bool value => .bool value

def ScalarOutput.native : ScalarOutput → Core.Value
  | .word value => .word value
  | .bool value => .bool value

def ScalarOutput.publicValue : ScalarOutput → SourceCorePublicValues.Value
  | .word value => .word value
  | .bool value => .bool value

theorem ScalarOutput.succeeded_value (scalar : ScalarOutput)
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {store : Core.Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation
      (.inRight .word scalar.native) store completion)
    (requested : checkpoint.ResultTypeAt scalar.sourceType) :
    completion.value = scalar.publicValue := by
  cases scalar with
  | word value => exact succeeded.word_value requested
  | bool value => exact succeeded_bool_value succeeded requested

theorem ScalarOutput.source_value (scalar : ScalarOutput)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome}
    {artifact : Artifact} {checkpoint : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt scalar.sourceType)
    (exported : completion.value = scalar.publicValue)
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world rawType scalar.nativeType
      faults outcome native) : outcome = .value scalar.source := by
  cases scalar with
  | word value => exact RecursiveNamedPublicWordResultMeaning.represented_word succeeded requested exported represented
  | bool value => exact represented_bool succeeded requested exported represented

theorem ScalarOutput.native_value (scalar : ScalarOutput)
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {rawType : TypeSystem.Ty}
    {payload : Core.Value}
    (represented : ValueRep checked registry functions mapping world rawType scalar.source payload scalar.nativeType) :
    payload = scalar.native := by
  cases scalar with
  | word value =>
    obtain ⟨actual, same, native⟩ := CompatibleExpressionPrimitives.word_fields represented
    exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  | bool value =>
    obtain ⟨actual, same, native⟩ := CompatibleExpressionPrimitives.bool_fields represented
    exact native.trans (congrArg Core.Value.bool (Dynamic.Value.bool.inj same).symm)

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics
abbrev Read := Tests.SourceCoreNamedBranch.Read
abbrev TypedNode := Tests.SourceCoreOperatorCalls.TypedNode

private theorem statementRoots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

structure ChooseShape (function : CheckedFunction) (signature : ProgramFunctionSignature) where
  firstParameter : TypeSystem.TypeParameterId
  secondParameter : TypeSystem.TypeParameterId
  different : firstParameter ≠ secondParameter
  firstOwner : firstParameter.owner = signature.id
  secondOwner : secondParameter.owner = signature.id
  first : TypedBinder
  second : TypedBinder
  bindersDifferent : second.id ≠ first.id
  read : Read function.typedBody first (.parameter firstParameter)
  statement : StatementNode
  scheme : signature.scheme = ⟨[firstParameter, secondParameter], [],
    .function (.product (.parameter firstParameter) (.parameter secondParameter)) (.parameter firstParameter)⟩
  inputTypes : signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]
  returns : signature.returnTypes = [.parameter firstParameter]
  inputs : function.typedBody.inputs = [first, second]
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = .parameter firstParameter

def ChooseShape.nodeList {function signature} (shape : ChooseShape function signature) : List Node :=
  [.expression shape.read.node, .statement shape.statement]

theorem ChooseShape.statementTyping {function signature}
    (shape : ChooseShape function signature) (signatures : ProgramSignatures) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := .parameter shape.firstParameter, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons _secondScheme secondExtended rest =>
      cases rest
      have parameters : lexical.typeParameters = [shape.firstParameter, shape.secondParameter] := by
        rw [secondExtended.context_fields.2.2.1, firstExtended.context_fields.2.2.1]
        simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
          Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.scheme]
      have owner : lexical.currentDeclaration = some signature.id := by
        rw [secondExtended.context_fields.2.1, firstExtended.context_fields.2.1]
        rfl
      have binders : TypeParameterBindersWellFormed lexical := by
        simp only [TypeParameterBindersWellFormed, parameters, owner]
        constructor
        · simp [shape.different]
        · intro parameter member
          rcases List.mem_cons.mp member with rfl | member
          · rw [shape.firstOwner]
          · cases List.mem_singleton.mp member
            rw [shape.secondOwner]
      have type : TypeAdmissible lexical (.parameter shape.firstParameter) :=
        ⟨binders, .parameter (by simp [parameters]) (by rw [owner, shape.firstOwner])⟩
      have readTyped := shape.read.typed firstScheme shape.firstRequirements type
        (by cases secondExtended; exact .tail shape.bindersDifferent firstExtended.local_self)
        (by cases secondExtended; exact .tail shape.bindersDifferent firstExtended.local_scheme_requirements_self)
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
        shape.statementForm readTyped shape.statementType)⟩

/-- The complete original two-parameter record includes the unused second result parameter. -/
structure DirectCall (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId)
    (firstType secondType : TypeSystem.Ty) (firstArgument secondArgument : ExpressionId) where
  callee : TypedNode source (.function (.product firstType secondType) firstType)
  value : TypedNode source firstType
  name : String
  instantiation : Frontend.SourceInference.DeclarationInstantiation
  calleeForm : callee.node.form = .reference name (.declaration instantiation)
  form : value.node.form = .call callee.node.id [firstArgument, secondArgument] (.declaration instantiation)
  different : firstParameter ≠ secondParameter
  scheme : signature.scheme = ⟨[firstParameter, secondParameter], [],
    .function (.product (.parameter firstParameter) (.parameter secondParameter)) (.parameter firstParameter)⟩
  inputs : signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]
  returns : signature.returnTypes = [.parameter firstParameter]
  exact : instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)],
    .function (.product firstType secondType) firstType, [], signature.parameterComptime, signature.returnComptime⟩

theorem DirectCall.typed {source signature firstParameter secondParameter firstType secondType firstArgument secondArgument}
    (call : DirectCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument)
    {context : SourceSemantics.Context} (member : signature ∈ context.signatures.functions)
    (firstFormed : TypeAdmissible context firstType) (secondFormed : TypeAdmissible context secondType)
    (firstTyped : ExpressionHasType source context firstArgument firstType)
    (secondTyped : ExpressionHasType source context secondArgument secondType) :
    ExpressionHasType source context call.value.node.id firstType := by
  have valid : SourceSemantics.DeclarationInstantiation.Admissible context call.instantiation := by
    rw [call.exact]
    refine .intro signature member rfl ?_ ?_ ?_ ?_ rfl rfl
    · refine ⟨by simp [call.scheme, call.different], ?_⟩
      simpa only [ParameterSubstitution.domain, List.map_cons, List.map_nil, call.scheme] using
        List.Perm.swap firstParameter secondParameter []
    · intro parameter replacement contained
      rcases List.mem_cons.mp contained with same | contained
      · cases same; exact secondFormed
      · cases List.mem_singleton.mp contained; exact firstFormed
    · simp [call.scheme, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.scheme]
  have application : DeclarationApplicationValid context call.instantiation [firstType, secondType] firstType [] := by
    refine .intro member valid ?_ ?_ ?_ ?_ ?_
    · simp [call.exact]
    · simp [call.exact, call.inputs, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, call.returns, TypeSystem.Ty.productMany, TypeSystem.ParameterSubstitution.apply, TypeSystem.ParameterSubstitution.lookup?, Ne.symm call.different]
    · simp [call.exact, TypeSystem.Ty.productMany]
    · simp [call.exact]
  have callee : DirectDeclarationCalleeValid context source call.callee.node.id call.instantiation :=
    .intro (lookupExpression?_sound call.callee.found) call.calleeForm valid
      (call.callee.type.trans (by rw [call.exact])) call.callee.requirements call.callee.coercions
  have typed : ExpressionHasType source context call.value.node.id call.value.node.type := by
    refine .intro (lookupExpression?_sound call.value.found)
      (call.form ▸ ExpressionFormHasRawType.directCall callee application (.cons firstTyped (.cons secondTyped (.nil _))))
      call.value.raw firstFormed (call.value.type.symm ▸ firstFormed) ?_
    rw [call.value.requirements, call.value.coercions, call.value.type]
    exact .directCall (.intro (.nil _) (.nil _) .nil rfl rfl)
  exact Eq.mp (congrArg (fun type => ExpressionHasType source context call.value.node.id type) call.value.type) typed

structure RootShape (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) where
  first : TypedBinder
  second : TypedBinder
  different : second.id ≠ first.id
  firstRead : Read function.typedBody first firstType
  secondRead : Read function.typedBody second secondType
  call : DirectCall function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id
  statement : StatementNode
  parameters : signature.scheme.parameters = []
  inputTypes : signature.parameterTypes = [firstType, secondType]
  returns : signature.returnTypes = [firstType]
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some call.value.node.id)
  statementType : statement.type = firstType

def RootShape.nodeList {function signature generic firstParameter secondParameter firstType secondType}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType) : List Node :=
  [.expression shape.firstRead.node, .expression shape.secondRead.node, .expression shape.call.callee.node,
   .expression shape.call.value.node, .statement shape.statement]

theorem RootShape.statementTyping {function signature generic firstParameter secondParameter firstType secondType}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType)
    (signatures : ProgramSignatures) (member : generic ∈ signatures.functions)
    (firstBuiltin : ∃ builtin, firstType = .constructor (.builtin builtin))
    (secondBuiltin : ∃ builtin, secondType = .constructor (.builtin builtin)) :
    CheckedBodyStatementsHaveType signatures signature function := by
  intro statements roots
  have same : statements = [shape.statement.id] := statementRoots_injective (roots.symm.trans shape.roots)
  subst statements
  rw [shape.returns]
  let facts : StatementFacts := {type := firstType, hasValue := true, sawReturn := true, control := .returned}
  refine ⟨BodyFacts.singleton facts, rfl, ?_⟩
  intro lexical extension
  rw [shape.inputs, shape.inputTypes] at extension
  cases extension with
  | cons firstScheme firstExtended rest =>
    cases rest with
    | cons secondScheme secondExtended rest =>
      cases rest
      have binders : TypeParameterBindersWellFormed lexical := by
        rw [TypeParameterBindersWellFormed, secondExtended.context_fields.2.2.1, firstExtended.context_fields.2.2.1]
        simp [checkedBodyContext, declarationContext, Context.ofSignatures, Context.forDeclaration,
          Context.withAssumptions, Context.withSolvedRequirements, Context.withResidualTypeVariables, shape.parameters]
      have fields : lexical.signatures = signatures := by
        rw [secondExtended.context_fields.1, firstExtended.context_fields.1]
        rfl
      have firstFormed : TypeAdmissible lexical firstType := by
        obtain ⟨builtin, rfl⟩ := firstBuiltin; exact ⟨binders, .builtin builtin⟩
      have secondFormed : TypeAdmissible lexical secondType := by
        obtain ⟨builtin, rfl⟩ := secondBuiltin; exact ⟨binders, .builtin builtin⟩
      have firstTyped := shape.firstRead.typed firstScheme shape.firstRequirements firstFormed
        (by cases secondExtended; exact .tail shape.different firstExtended.local_self)
        (by cases secondExtended; exact .tail shape.different firstExtended.local_scheme_requirements_self)
      have secondTyped := shape.secondRead.typed secondScheme shape.secondRequirements secondFormed
        secondExtended.local_self secondExtended.local_scheme_requirements_self
      have callTyped := shape.call.typed (fields ▸ member) firstFormed secondFormed firstTyped secondTyped
      exact ⟨_, .singleton (.returnValue (lookupStatement?_sound shape.statementFound)
        shape.statementForm callTyped shape.statementType)⟩


private def observed (p : Prop) [Decidable p] (message : String) : IO (PLift p) :=
  if witness : p then pure ⟨witness⟩ else throw (IO.userError message)

def observeChoose (function : CheckedFunction) (signature : ProgramFunctionSignature) : IO (ChooseShape function signature) := do
  let [firstParameter, secondParameter] := signature.scheme.parameters | throw (IO.userError "choose parameters")
  let [first, second] := function.typedBody.inputs | throw (IO.userError "choose binders")
  let [.expression node, .statement statement] := function.typedBody.nodes | throw (IO.userError "choose nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first node (.parameter firstParameter)
  let ⟨different⟩ ← observed (firstParameter ≠ secondParameter) "choose different"
  let ⟨firstOwner⟩ ← observed (firstParameter.owner = signature.id) "choose firstOwner"
  let ⟨secondOwner⟩ ← observed (secondParameter.owner = signature.id) "choose secondOwner"
  let ⟨bindersDifferent⟩ ← observed (second.id ≠ first.id) "choose bindersDifferent"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[firstParameter, secondParameter], [], .function (.product (.parameter firstParameter) (.parameter secondParameter)) (.parameter firstParameter)⟩) "choose scheme"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]) "choose inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.parameter firstParameter]) "choose returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "choose inputs"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "choose firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "choose secondRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "choose roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "choose statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "choose statementForm"
  let ⟨statementType⟩ ← observed (statement.type = .parameter firstParameter) "choose statementType"
  return {firstParameter, secondParameter, first, second, read, statement, different, firstOwner, secondOwner, bindersDifferent, scheme, inputTypes, returns, inputs, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}

def observeDirect (source : TypedSource) (signature : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty)
    (firstArgument secondArgument : ExpressionId) (callee value : ExpressionNode) :
    IO (DirectCall source signature firstParameter secondParameter firstType secondType firstArgument secondArgument) := do
  let callee ← Tests.SourceCoreOperatorCalls.observeNode source callee (.function (.product firstType secondType) firstType)
  let value ← Tests.SourceCoreOperatorCalls.observeNode source value firstType
  let .reference name (.declaration instantiation) := callee.node.form | throw (IO.userError "generic direct callee")
  let ⟨calleeForm⟩ ← observed (callee.node.form = .reference name (.declaration instantiation)) "generic direct calleeForm"
  let ⟨form⟩ ← observed (value.node.form = .call callee.node.id [firstArgument, secondArgument] (.declaration instantiation)) "generic direct form"
  let ⟨different⟩ ← observed (firstParameter ≠ secondParameter) "generic direct different"
  let ⟨scheme⟩ ← observed (signature.scheme = ⟨[firstParameter, secondParameter], [], .function (.product (.parameter firstParameter) (.parameter secondParameter)) (.parameter firstParameter)⟩) "generic direct scheme"
  let ⟨inputs⟩ ← observed (signature.parameterTypes = [.parameter firstParameter, .parameter secondParameter]) "generic direct inputs"
  let ⟨returns⟩ ← observed (signature.returnTypes = [.parameter firstParameter]) "generic direct returns"
  let ⟨exact⟩ ← observed (instantiation = ⟨signature.id, [(secondParameter, secondType), (firstParameter, firstType)], .function (.product firstType secondType) firstType, [], signature.parameterComptime, signature.returnComptime⟩) "generic direct exact"
  return {callee, value, name, instantiation, calleeForm, form, different, scheme, inputs, returns, exact}

def observeRoot (function : CheckedFunction) (signature generic : ProgramFunctionSignature)
    (firstParameter secondParameter : TypeSystem.TypeParameterId) (firstType secondType : TypeSystem.Ty) :
    IO (RootShape function signature generic firstParameter secondParameter firstType secondType) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "root inputs")
  let [.expression readFirst, .expression readSecond, .expression callee, .expression value, .statement statement] := function.typedBody.nodes
    | throw (IO.userError "root nodes")
  let firstRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first readFirst firstType
  let secondRead ← Tests.SourceCoreNamedBranch.observeRead function.typedBody second readSecond secondType
  let call ← observeDirect function.typedBody generic firstParameter secondParameter firstType secondType firstRead.node.id secondRead.node.id callee value
  let ⟨different⟩ ← observed (second.id ≠ first.id) "generic root different"
  let ⟨parameters⟩ ← observed (signature.scheme.parameters = []) "generic root parameters"
  let ⟨inputTypes⟩ ← observed (signature.parameterTypes = [firstType, secondType]) "generic root inputTypes"
  let ⟨returns⟩ ← observed (signature.returnTypes = [firstType]) "generic root returns"
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "generic root inputs"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "generic root firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "generic root secondScheme"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "generic root firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "generic root secondRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "generic root roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "generic root statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some call.value.node.id)) "generic root statementForm"
  let ⟨statementType⟩ ← observed (statement.type = firstType) "generic root statementType"
  return {first, second, firstRead, secondRead, call, statement, different, parameters, inputTypes, returns, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType}

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function choose<A, B>(a: A, b: B) returns (A) { return a; }",
    "function wordRoot(value: Word, flag: Bool) returns (Word) { return choose(value, flag); }",
    "function boolRoot(flag: Bool, value: Word) returns (Bool) { return choose(flag, value); }"]}] }

structure CheckedFixture where
  program : CheckedProgram
  checked : checkProgram workspace 1000 = .ok program
  wellFormed : ProgramWellFormed (Program.ofChecked program)
  chooseFunction : CheckedFunction
  wordFunction : CheckedFunction
  boolFunction : CheckedFunction
  chooseSignature : ProgramFunctionSignature
  wordSignature : ProgramFunctionSignature
  boolSignature : ProgramFunctionSignature
  functions : program.functions = [chooseFunction, wordFunction, boolFunction]
  signatures : program.signatures.functions = [chooseSignature, wordSignature, boolSignature]
  methods : program.methods = []
  chooseDeclaration : chooseFunction.declaration = chooseSignature.id
  wordDeclaration : wordFunction.declaration = wordSignature.id
  boolDeclaration : boolFunction.declaration = boolSignature.id
  chooseWord : chooseSignature.id ≠ wordSignature.id
  chooseBool : chooseSignature.id ≠ boolSignature.id
  wordBool : wordSignature.id ≠ boolSignature.id
  chooseShape : ChooseShape chooseFunction chooseSignature
  wordShape : RootShape wordFunction wordSignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter .word .bool
  boolShape : RootShape boolFunction boolSignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter .bool .word
  chooseNodes : chooseFunction.typedBody.nodes = chooseShape.nodeList
  wordNodes : wordFunction.typedBody.nodes = wordShape.nodeList
  boolNodes : boolFunction.typedBody.nodes = boolShape.nodeList

def checkedFixture : IO CheckedFixture := do
  match checked : checkProgram workspace 1000 with
  | .error error => throw (IO.userError (reprStr error))
  | .ok program =>
    match functions : program.functions, signatures : program.signatures.functions with
    | [chooseFunction, wordFunction, boolFunction], [chooseSignature, wordSignature, boolSignature] =>
      let chooseShape ← observeChoose chooseFunction chooseSignature
      let wordShape ← observeRoot wordFunction wordSignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter .word .bool
      let boolShape ← observeRoot boolFunction boolSignature chooseSignature chooseShape.firstParameter chooseShape.secondParameter .bool .word
      let ⟨methods⟩ ← observed (program.methods = []) "generic fixture methods"
      let ⟨chooseDeclaration⟩ ← observed (chooseFunction.declaration = chooseSignature.id) "generic fixture chooseDeclaration"
      let ⟨wordDeclaration⟩ ← observed (wordFunction.declaration = wordSignature.id) "generic fixture wordDeclaration"
      let ⟨boolDeclaration⟩ ← observed (boolFunction.declaration = boolSignature.id) "generic fixture boolDeclaration"
      let ⟨chooseWord⟩ ← observed (chooseSignature.id ≠ wordSignature.id) "generic fixture chooseWord"
      let ⟨chooseBool⟩ ← observed (chooseSignature.id ≠ boolSignature.id) "generic fixture chooseBool"
      let ⟨wordBool⟩ ← observed (wordSignature.id ≠ boolSignature.id) "generic fixture wordBool"
      let ⟨chooseNodes⟩ ← observed (chooseFunction.typedBody.nodes = chooseShape.nodeList) "generic fixture chooseNodes"
      let ⟨wordNodes⟩ ← observed (wordFunction.typedBody.nodes = wordShape.nodeList) "generic fixture wordNodes"
      let ⟨boolNodes⟩ ← observed (boolFunction.typedBody.nodes = boolShape.nodeList) "generic fixture boolNodes"
      let deep : CheckedProgramBodiesHaveStatementTyping program 1000 := {
        functions := by
          intro actual member candidate candidateMember accepted
          have identity := checkFunctionBody_success_declaration accepted
          simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
          simp only [signatures, List.mem_cons, List.not_mem_nil, or_false] at candidateMember
          rcases member with rfl | rfl | rfl <;> rcases candidateMember with rfl | rfl | rfl
          · exact chooseShape.statementTyping program.signatures
          · exact False.elim (chooseWord (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (chooseDeclaration.symm.trans identity))
          · exact False.elim (chooseWord (identity.symm.trans wordDeclaration))
          · exact wordShape.statementTyping program.signatures (by simp [signatures]) ⟨.word, rfl⟩ ⟨.bool, rfl⟩
          · exact False.elim (wordBool (wordDeclaration.symm.trans identity))
          · exact False.elim (chooseBool (identity.symm.trans boolDeclaration))
          · exact False.elim (wordBool (identity.symm.trans boolDeclaration))
          · exact boolShape.statementTyping program.signatures (by simp [signatures]) ⟨.bool, rfl⟩ ⟨.word, rfl⟩
        methods := by intro method member; simp only [methods, List.not_mem_nil] at member }
      return {program, checked, wellFormed := programWellFormed_ofCheckProgram_statements checked deep, chooseFunction, wordFunction, boolFunction, chooseSignature, wordSignature, boolSignature, functions, signatures, methods, chooseDeclaration, wordDeclaration, boolDeclaration, chooseWord, chooseBool, wordBool, chooseShape, wordShape, boolShape, chooseNodes, wordNodes, boolNodes}
    | _, _ => throw (IO.userError "generic direct declarations")
end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectFixture
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics

structure CompiledFixture extends CheckedFixture where
  seeds : List SourceCompiler.Seed
  options : SourceCompiler.Options
  facadeCompiled : SourceCompiler.Compiled
  accepted : SourceCompiler.compileChecked program seeds options = .ok facadeCompiled
  recipe : SourceCoreIndexedSession.Recipe
  issued : CoreLowering.RecursiveNamedPreparedStageContracts.PublicRecipe facadeCompiled recipe
  sameProgram : recipe.compiled.sourceProgram = program
  recipePrepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe

def compiledFixture : IO CompiledFixture := do
  let checked ← checkedFixture
  let seeds := [SourceCompiler.Seed.declaration checked.wordSignature.id, SourceCompiler.Seed.declaration checked.boolSignature.id]
  let options : SourceCompiler.Options := {checkingFuel := 1000, compilationFuel := 100}
  match generated : SourceCoreCompiler.compileChecked checked.program seeds options with
  | .error error => throw (IO.userError (reprStr error))
  | .ok source =>
    match selected : source.artifact? with
    | none => throw (IO.userError "factory cached artifact missing")
    | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (IO.userError (reprStr error))
      | .ok recipe =>
        match facade : SourceCoreExecution.prepare source with
        | .error error => throw (IO.userError (reprStr error))
        | .ok facadeCompiled =>
          have accepted : SourceCompiler.compileChecked checked.program seeds options = .ok facadeCompiled := by
            simpa only [SourceCoreExecution.compileChecked, generated, Except.mapError,
              bind, Except.bind] using facade
          have sameProgram : recipe.compiled.sourceProgram = checked.program :=
            (congrArg (·.sourceProgram) (SourceCoreIndexedSession.Recipe.prepare_compiled prepared)).trans
              ((source.artifact_fields selected).1.trans (SourceCoreCompiler.compileChecked_program generated))
          return {
            toCheckedFixture := checked
            seeds := seeds
            options := options
            facadeCompiled := facadeCompiled
            accepted := accepted
            recipe := recipe
            issued := CoreLowering.RecursiveNamedPreparedStageContracts.public_preparation selected prepared facade
            sameProgram := sameProgram
            recipePrepared := by rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]; exact prepared }

theorem CompiledFixture.prepared (fixture : CompiledFixture)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ fixture.recipe.compiled.validationPlan.specializations) :
    Nonempty (CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row) :=
  CoreLowering.RecursiveNamedPublicSpecializationMeaning.of_public_compile fixture.accepted fixture.issued member

theorem CompiledFixture.source_wellFormed (fixture : CompiledFixture) :
    ProgramWellFormed (Program.ofChecked fixture.recipe.compiled.sourceProgram) := by
  rw [fixture.sameProgram]
  exact fixture.wellFormed

structure ActualHeader (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) where
  prepared : CoreLowering.RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled row
  header : CoreLowering.CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
    (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  aligned : CoreLowering.RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared
    (CoreLowering.CallableNamedCanonicalOrder.retainedInstantiation row) header
  diagnostic : CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared



open CoreLowering

theorem ActualHeader.terminal {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) (expression : ExpressionId) (statement : StatementNode)
    (roots : row.function.typedBody.roots = [.statement statement.id])
    (found : row.function.typedBody.lookupStatement? statement.id = some statement)
    (form : statement.form = .returnStmt (some expression)) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared ∧
      terminal.expression = expression ∧ terminal.certificate =
        CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
          (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
          terminal.expression terminal.receipt.child := by
  have source : actual.header.function.source = row.function.typedBody := by
    rw [actual.aligned.function]
    exact congrArg (fun specialized => specialized.function.typedBody) actual.prepared.same
  have body : actual.header.function.body = [statement.id] := by
    rw [actual.aligned.function]
    change actual.prepared.compilation.statements = [statement.id]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, roots] at accepted
    exact (Except.ok.inj accepted).symm
  have terminalShape : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      actual.header.function.source expression actual.header.function.body := by
    rw [source, body]
    exact .returning [] found form
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [actual.aligned.policy]; rfl) terminalShape actual.aligned.accepted
  let terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header := {
    row := row
    prepared := actual.prepared
    instantiation := CallableNamedCanonicalOrder.retainedInstantiation row
    aligned := actual.aligned
    layouts := actual.aligned.layouts
    expression := expression
    receipt := receipt
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (actual.header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression receipt.child
    certifies := by
      intro child generated
      have same : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, same⟩ }
  exact ⟨terminal, actual.diagnostic, rfl, rfl⟩



/-- Each observation refers to an actual compiler row, unique physical slot,
and original source declaration. Public roots additionally retain an entry. -/
structure ObservedRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) where
  row : SourceSpecialization.SpecializedFunction
  member : row ∈ fixture.recipe.compiled.validationPlan.specializations
  sourceOwner : row.function.typedBody.owner = signature.id
  scalarRange : row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true
  keyOwner : row.key.declaration = signature.id
  assumptions : row.assumptions = []
  ordinary : row.function.returnComptime = false
  inputsOrdinary : ∀ binder, binder ∈ row.function.typedBody.inputs → binder.comptime = false
  target : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
    (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key
  global : SourceCoreCalls.Signature
  index : Nat
  slot : CallableNamedMetadata.Slot fixture.recipe.compiled.indexed.base.globals index global
  globalKey : global.key = row.key

structure ObservedRoot (fixture : CompiledFixture) (signature : ProgramFunctionSignature) extends ObservedRow fixture signature where
  entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts
  entryMember : entry ∈ fixture.recipe.compiled.indexed.entries
  entryKey : entry.key = row.key

private def observeTarget (fixture : CompiledFixture) (row : SourceSpecialization.SpecializedFunction) :
    IO (PLift (SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)) := do
  match accepted : SourceCompilationPlan.exactInstantiationKey fixture.recipe.compiled.indexed.base.plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) with
  | .error error => throw (IO.userError (reprStr error))
  | .ok key =>
    let ⟨same⟩ ← observed (key = row.key) "reuse exact key"
    return ⟨by rw [accepted, same]⟩

def observeRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) (arguments : List TypeSystem.Ty) :
    IO (ObservedRow fixture signature) := do
  match found : fixture.recipe.compiled.validationPlan.specializations.find?
      (fun row => decide (row.function.typedBody.owner = signature.id ∧ row.key.arguments = arguments)) with
  | none => throw (IO.userError "reuse specialization missing")
  | some row =>
    let ⟨sourceOwner⟩ ← observed (row.function.typedBody.owner = signature.id) "reuse source owner"
    let ⟨scalarRange⟩ ← observed (row.parameterSubstitution.all (fun entry => decide (entry.2 = .word ∨ entry.2 = .bool)) = true) "generic complete raw range"
    let ⟨keyOwner⟩ ← observed (row.key.declaration = signature.id) "generic row key owner"
    let ⟨assumptions⟩ ← observed (row.assumptions = []) "direct row assumptions"
    let ⟨ordinary⟩ ← observed (row.function.returnComptime = false) "reuse return marker"
    let ⟨ordinaryInputs⟩ ← observed (row.function.typedBody.inputs.all (fun binder => !binder.comptime) = true) "reuse parameter markers"
    let ⟨target⟩ ← observeTarget fixture row
    match slot : fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = row.key)) with
    | [(global, index)] =>
      let ⟨globalKey⟩ ← observed (global.key = row.key) "reuse global key"
      return {
        row := row
        member := List.mem_of_find?_eq_some found
        sourceOwner := sourceOwner
        scalarRange := scalarRange
        keyOwner := keyOwner
        assumptions := assumptions
        ordinary := ordinary
        inputsOrdinary := by
          intro binder member
          have selected := List.all_eq_true.mp ordinaryInputs binder member
          cases same : binder.comptime <;> simp_all
        target := target
        global := global
        index := index
        slot := by unfold CallableNamedMetadata.Slot; rw [globalKey]; exact slot
        globalKey := globalKey
        }
    | _ => throw (IO.userError "reuse unique global slot")


def observeRootRow (fixture : CompiledFixture) (signature : ProgramFunctionSignature) : IO (ObservedRoot fixture signature) := do
  let row ← observeRow fixture signature []
  match entryFound : fixture.recipe.compiled.indexed.entries.find? (fun entry => decide (entry.key = row.row.key)) with
  | none => throw (IO.userError "public root entry missing")
  | some entry =>
    let ⟨entryKey⟩ ← observed (entry.key = row.row.key) "public root entry key"
    return {toObservedRow := row, entry, entryMember := List.mem_of_find?_eq_some entryFound, entryKey}

structure SelectedShape (function : CheckedFunction) (firstType secondType : TypeSystem.Ty) where
  first : TypedBinder
  second : TypedBinder
  read : Read function.typedBody first firstType
  statement : StatementNode
  inputs : function.typedBody.inputs = [first, second]
  firstScheme : first.scheme = .mono firstType
  secondScheme : second.scheme = .mono secondType
  firstRequirements : first.schemeRequirements = []
  secondRequirements : second.schemeRequirements = []
  roots : function.typedBody.roots = [.statement statement.id]
  statementFound : function.typedBody.lookupStatement? statement.id = some statement
  statementForm : statement.form = .returnStmt (some read.node.id)
  statementType : statement.type = firstType
  resultType : function.inferredBodyType = firstType

def SelectedShape.nodeList {function firstType secondType} (shape : SelectedShape function firstType secondType) : List Node :=
  [.expression shape.read.node, .statement shape.statement]

def observeSelected (function : CheckedFunction) (firstType secondType : TypeSystem.Ty) : IO (SelectedShape function firstType secondType) := do
  let [first, second] := function.typedBody.inputs | throw (IO.userError "generic selected inputs")
  let [.expression node, .statement statement] := function.typedBody.nodes | throw (IO.userError "generic selected nodes")
  let read ← Tests.SourceCoreNamedBranch.observeRead function.typedBody first node firstType
  let ⟨inputs⟩ ← observed (function.typedBody.inputs = [first, second]) "selected inputs"
  let ⟨firstScheme⟩ ← observed (first.scheme = .mono firstType) "selected firstScheme"
  let ⟨secondScheme⟩ ← observed (second.scheme = .mono secondType) "selected secondScheme"
  let ⟨firstRequirements⟩ ← observed (first.schemeRequirements = []) "selected firstRequirements"
  let ⟨secondRequirements⟩ ← observed (second.schemeRequirements = []) "selected secondRequirements"
  let ⟨roots⟩ ← observed (function.typedBody.roots = [.statement statement.id]) "selected roots"
  let ⟨statementFound⟩ ← observed (function.typedBody.lookupStatement? statement.id = some statement) "selected statementFound"
  let ⟨statementForm⟩ ← observed (statement.form = .returnStmt (some read.node.id)) "selected statementForm"
  let ⟨statementType⟩ ← observed (statement.type = firstType) "selected statementType"
  let ⟨resultType⟩ ← observed (function.inferredBodyType = firstType) "selected resultType"
  return {first, second, read, statement, inputs, firstScheme, secondScheme, firstRequirements, secondRequirements, roots, statementFound, statementForm, statementType, resultType}

structure ObservedProgram (fixture : CompiledFixture) where
  wordRow : ObservedRoot fixture fixture.wordSignature
  boolRow : ObservedRoot fixture fixture.boolSignature
  chooseWordRow : ObservedRow fixture fixture.chooseSignature
  chooseBoolRow : ObservedRow fixture fixture.chooseSignature
  globalsLength : fixture.recipe.compiled.indexed.base.globals.length = 4
  wordBool : wordRow.index ≠ boolRow.index
  wordChooseWord : wordRow.index ≠ chooseWordRow.index
  wordChooseBool : wordRow.index ≠ chooseBoolRow.index
  boolChooseWord : boolRow.index ≠ chooseWordRow.index
  boolChooseBool : boolRow.index ≠ chooseBoolRow.index
  chooseWordChooseBool : chooseWordRow.index ≠ chooseBoolRow.index
  wordShape : RootShape wordRow.row.function fixture.wordSignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .word .bool
  boolShape : RootShape boolRow.row.function fixture.boolSignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .bool .word
  chooseWordShape : SelectedShape chooseWordRow.row.function .word .bool
  chooseBoolShape : SelectedShape chooseBoolRow.row.function .bool .word
  wordNodes : wordRow.row.function.typedBody.nodes = wordShape.nodeList
  boolNodes : boolRow.row.function.typedBody.nodes = boolShape.nodeList
  chooseWordNodes : chooseWordRow.row.function.typedBody.nodes = chooseWordShape.nodeList
  chooseBoolNodes : chooseBoolRow.row.function.typedBody.nodes = chooseBoolShape.nodeList
  wordResultType : wordRow.row.function.inferredBodyType = .word
  boolResultType : boolRow.row.function.inferredBodyType = .bool
  wordKey : wordRow.row.key = ⟨fixture.wordSignature.id, []⟩
  boolKey : boolRow.row.key = ⟨fixture.boolSignature.id, []⟩
  chooseWordKey : chooseWordRow.row.key = ⟨fixture.chooseSignature.id, [.word, .bool]⟩
  chooseBoolKey : chooseBoolRow.row.key = ⟨fixture.chooseSignature.id, [.bool, .word]⟩
  wordParameters : wordRow.row.parameterSubstitution = []
  boolParameters : boolRow.row.parameterSubstitution = []
  chooseWordParameters : chooseWordRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .word), (fixture.chooseShape.secondParameter, .bool)]
  chooseBoolParameters : chooseBoolRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .bool), (fixture.chooseShape.secondParameter, .word)]
  wordInstantiation : wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row
  boolInstantiation : boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row
  noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = []
  profile : fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true

def observeProgram (fixture : CompiledFixture) : IO (ObservedProgram fixture) := do
  let wordRow ← observeRootRow fixture fixture.wordSignature
  let boolRow ← observeRootRow fixture fixture.boolSignature
  let chooseWordRow ← observeRow fixture fixture.chooseSignature [.word, .bool]
  let chooseBoolRow ← observeRow fixture fixture.chooseSignature [.bool, .word]
  let wordShape ← observeRoot wordRow.row.function fixture.wordSignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .word .bool
  let boolShape ← observeRoot boolRow.row.function fixture.boolSignature fixture.chooseSignature fixture.chooseShape.firstParameter fixture.chooseShape.secondParameter .bool .word
  let chooseWordShape ← observeSelected chooseWordRow.row.function .word .bool
  let chooseBoolShape ← observeSelected chooseBoolRow.row.function .bool .word
  let ⟨globalsLength⟩ ← observed (fixture.recipe.compiled.indexed.base.globals.length = 4) "generic program globalsLength"
  let ⟨wordBool⟩ ← observed (wordRow.index ≠ boolRow.index) "generic program wordBool"
  let ⟨wordChooseWord⟩ ← observed (wordRow.index ≠ chooseWordRow.index) "generic program wordChooseWord"
  let ⟨wordChooseBool⟩ ← observed (wordRow.index ≠ chooseBoolRow.index) "generic program wordChooseBool"
  let ⟨boolChooseWord⟩ ← observed (boolRow.index ≠ chooseWordRow.index) "generic program boolChooseWord"
  let ⟨boolChooseBool⟩ ← observed (boolRow.index ≠ chooseBoolRow.index) "generic program boolChooseBool"
  let ⟨chooseWordChooseBool⟩ ← observed (chooseWordRow.index ≠ chooseBoolRow.index) "generic program chooseWordChooseBool"
  let ⟨wordNodes⟩ ← observed (wordRow.row.function.typedBody.nodes = wordShape.nodeList) "generic program wordNodes"
  let ⟨boolNodes⟩ ← observed (boolRow.row.function.typedBody.nodes = boolShape.nodeList) "generic program boolNodes"
  let ⟨chooseWordNodes⟩ ← observed (chooseWordRow.row.function.typedBody.nodes = chooseWordShape.nodeList) "generic program chooseWordNodes"
  let ⟨chooseBoolNodes⟩ ← observed (chooseBoolRow.row.function.typedBody.nodes = chooseBoolShape.nodeList) "generic program chooseBoolNodes"
  let ⟨wordResultType⟩ ← observed (wordRow.row.function.inferredBodyType = .word) "generic program wordResultType"
  let ⟨boolResultType⟩ ← observed (boolRow.row.function.inferredBodyType = .bool) "generic program boolResultType"
  let ⟨wordKey⟩ ← observed (wordRow.row.key = ⟨fixture.wordSignature.id, []⟩) "generic program wordKey"
  let ⟨boolKey⟩ ← observed (boolRow.row.key = ⟨fixture.boolSignature.id, []⟩) "generic program boolKey"
  let ⟨chooseWordKey⟩ ← observed (chooseWordRow.row.key = ⟨fixture.chooseSignature.id, [.word, .bool]⟩) "generic program chooseWordKey"
  let ⟨chooseBoolKey⟩ ← observed (chooseBoolRow.row.key = ⟨fixture.chooseSignature.id, [.bool, .word]⟩) "generic program chooseBoolKey"
  let ⟨wordParameters⟩ ← observed (wordRow.row.parameterSubstitution = []) "generic program wordParameters"
  let ⟨boolParameters⟩ ← observed (boolRow.row.parameterSubstitution = []) "generic program boolParameters"
  let ⟨chooseWordParameters⟩ ← observed (chooseWordRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .word), (fixture.chooseShape.secondParameter, .bool)]) "generic program chooseWordParameters"
  let ⟨chooseBoolParameters⟩ ← observed (chooseBoolRow.row.parameterSubstitution = [(fixture.chooseShape.firstParameter, .bool), (fixture.chooseShape.secondParameter, .word)]) "generic program chooseBoolParameters"
  let ⟨wordInstantiation⟩ ← observed (wordShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseWordRow.row) "generic exact wordInstantiation"
  let ⟨boolInstantiation⟩ ← observed (boolShape.call.instantiation = CallableNamedCanonicalOrder.retainedInstantiation chooseBoolRow.row) "generic exact boolInstantiation"
  let ⟨noLocals⟩ ← observed (fixture.recipe.compiled.indexed.base.locals.bindings = []) "generic program noLocals"
  let ⟨profile⟩ ← observed (fixture.recipe.compiled.compatible.checked.catalog.callableContracts = true) "generic program profile"
  return {wordRow, boolRow, chooseWordRow, chooseBoolRow, wordShape, boolShape, chooseWordShape, chooseBoolShape, globalsLength, wordBool, wordChooseWord, wordChooseBool, boolChooseWord, boolChooseBool, chooseWordChooseBool, wordNodes, boolNodes, chooseWordNodes, chooseBoolNodes, wordResultType, boolResultType, wordKey, boolKey, chooseWordKey, chooseBoolKey, wordParameters, boolParameters, chooseWordParameters, chooseBoolParameters, wordInstantiation, boolInstantiation, noLocals, profile}

theorem ObservedRow.prepared_slot {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature)
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared fixture.recipe.compiled observed.row) :
    prepared.named.signature = observed.global ∧ prepared.index = observed.index := by
  have selected := CallableIndexedPreparedInventories.cached_global_at fixture.recipe.compiled prepared.selected
  have member : (prepared.named.signature, prepared.index) ∈
      fixture.recipe.compiled.indexed.base.globals.zipIdx.filter
        (fun item => decide (item.1.key = observed.global.key)) := by
    refine List.mem_filter.mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr selected, ?_⟩
    simp only [observed.globalKey, RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared,
      decide_true]
  rw [observed.slot] at member
  exact Prod.mk.inj (List.mem_singleton.mp member)

theorem ObservedRow.issue {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (observed : ObservedRow fixture signature) :
    ∃ input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled,
      input.row = observed.row ∧
      ∃ packet : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued input,
      ∃ actual : ActualHeader fixture observed.row,
        actual.header = packet.header ∧ actual.header.slot = observed.index ∧ actual.header.named.signature = observed.global := by
  obtain ⟨prepared⟩ := fixture.prepared observed.member
  obtain ⟨signatureEq, indexEq⟩ := observed.prepared_slot prepared
  have range : SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures fixture.recipe.compiled.sourceProgram.signatures) observed.row.parameterSubstitution := by
    intro parameter replacement member
    have scalar := of_decide_eq_true (List.all_eq_true.mp observed.scalarRange (parameter, replacement) member)
    rcases scalar with rfl | rfl
    · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .word⟩
    · exact ⟨by simp [TypeParameterBindersWellFormed, Context.ofSignatures], .builtin .bool⟩
  let input : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled := {
    row := observed.row
    prepared := prepared
    range := range
    ordinaryReturn := observed.ordinary
    ordinaryParameters := observed.inputsOrdinary
    target := by rw [RecursiveNamedPreparedCallEvidence.Prepared.signature_key prepared]; exact observed.target
    slot := by rw [signatureEq, indexEq]; exact observed.slot }
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedFiniteNamedInventories.issue fixture.source_wellFormed input
  let actual : ActualHeader fixture observed.row := {
    prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued prepared packet.selected
    header := packet.header
    aligned := packet.aligned
    diagnostic := ⟨⟨packet.selected.diagnostics, packet.selected.found, rfl⟩⟩ }
  exact ⟨input, rfl, packet, actual, rfl, actual.aligned.slot.trans indexEq,
    (congrArg (·.signature) actual.aligned.named).trans signatureEq⟩

theorem ObservedProgram.inventory {fixture : CompiledFixture} (observed : ObservedProgram fixture) :
    ∃ (wordInput boolInput chooseWordInput chooseBoolInput : CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled),
      wordInput.row = observed.wordRow.row ∧ boolInput.row = observed.boolRow.row ∧ chooseWordInput.row = observed.chooseWordRow.row ∧ chooseBoolInput.row = observed.chooseBoolRow.row ∧
      ∃ (wordPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued wordInput)
        (boolPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued boolInput)
        (chooseWordPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued chooseWordInput)
        (chooseBoolPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued chooseBoolInput),
      ∃ (wordHeader : ActualHeader fixture observed.wordRow.row)
        (boolHeader : ActualHeader fixture observed.boolRow.row)
        (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
        (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row),
        wordHeader.header = wordPacket.header ∧ boolHeader.header = boolPacket.header ∧ chooseWordHeader.header = chooseWordPacket.header ∧ chooseBoolHeader.header = chooseBoolPacket.header ∧
        RecursiveNamedCatalogNativeContexts.Complete
          (values := .initial fixture.recipe.compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
          (CallableIndexedOwnedPreparedFiniteNamedInventories.headers (.cons wordPacket (.cons boolPacket (.cons chooseWordPacket (.cons chooseBoolPacket .nil))))) := by
  obtain ⟨wordInput, wordRow, wordPacket, wordHeader, wordEq, wordSlot, wordSignature⟩ := observed.wordRow.issue
  obtain ⟨boolInput, boolRow, boolPacket, boolHeader, boolEq, boolSlot, boolSignature⟩ := observed.boolRow.issue
  obtain ⟨chooseWordInput, chooseWordRow, chooseWordPacket, chooseWordHeader, chooseWordEq, chooseWordSlot, chooseWordSignature⟩ := observed.chooseWordRow.issue
  obtain ⟨chooseBoolInput, chooseBoolRow, chooseBoolPacket, chooseBoolHeader, chooseBoolEq, chooseBoolSlot, chooseBoolSignature⟩ := observed.chooseBoolRow.issue
  refine ⟨wordInput, boolInput, chooseWordInput, chooseBoolInput, wordRow, boolRow, chooseWordRow, chooseBoolRow, wordPacket, boolPacket, chooseWordPacket, chooseBoolPacket, wordHeader, boolHeader, chooseWordHeader, chooseBoolHeader, wordEq, boolEq, chooseWordEq, chooseBoolEq, ?_⟩
  have wordBound := (List.getElem?_eq_some_iff.mp observed.wordRow.slot.selected).1
  have boolBound := (List.getElem?_eq_some_iff.mp observed.boolRow.slot.selected).1
  have chooseWordBound := (List.getElem?_eq_some_iff.mp observed.chooseWordRow.slot.selected).1
  have chooseBoolBound := (List.getElem?_eq_some_iff.mp observed.chooseBoolRow.slot.selected).1
  rw [observed.globalsLength] at wordBound boolBound chooseWordBound chooseBoolBound
  intro index signature found
  have bound := (List.getElem?_eq_some_iff.mp found).1
  rw [observed.globalsLength] at bound
  have casesIndex : index = observed.wordRow.index ∨ index = observed.boolRow.index ∨ index = observed.chooseWordRow.index ∨ index = observed.chooseBoolRow.index := by
    have wordBool := observed.wordBool
    have wordChooseWord := observed.wordChooseWord
    have wordChooseBool := observed.wordChooseBool
    have boolChooseWord := observed.boolChooseWord
    have boolChooseBool := observed.boolChooseBool
    have chooseWordChooseBool := observed.chooseWordChooseBool
    omega
  rcases casesIndex with same | same | same | same
  · refine ⟨wordHeader.header, ?_, wordSlot.trans same.symm, ?_⟩
    · rw [wordEq]; exact .head _
    · rw [same, observed.wordRow.slot.selected] at found
      exact wordSignature.trans (Option.some.inj found)
  · refine ⟨boolHeader.header, ?_, boolSlot.trans same.symm, ?_⟩
    · rw [boolEq]; exact .tail _ (.head _)
    · rw [same, observed.boolRow.slot.selected] at found
      exact boolSignature.trans (Option.some.inj found)
  · refine ⟨chooseWordHeader.header, ?_, chooseWordSlot.trans same.symm, ?_⟩
    · rw [chooseWordEq]; exact .tail _ (.tail _ (.head _))
    · rw [same, observed.chooseWordRow.slot.selected] at found
      exact chooseWordSignature.trans (Option.some.inj found)
  · refine ⟨chooseBoolHeader.header, ?_, chooseBoolSlot.trans same.symm, ?_⟩
    · rw [chooseBoolEq]; exact .tail _ (.tail _ (.tail _ (.head _)))
    · rw [same, observed.chooseBoolRow.slot.selected] at found
      exact chooseBoolSignature.trans (Option.some.inj found)
structure ObservedStages (fixture : CompiledFixture)
    {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named observed.row.key)
  native : SourceCoreGeneralFunctions.CallableContext
  present : fixture.recipe.compiled.indexed.base.callableContext = some native
  sidecar : SourceCoreStageContracts.Sidecar
  issued : SourceCoreStageContracts.prepareSidecar
    fixture.recipe.compiled.indexed.base.plan observed.row.key = .ok sidecar

def observeStages (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedStages fixture observed) := do
  match present : fixture.recipe.compiled.indexed.base.callableContext with
  | none => throw (IO.userError "factory callable context missing")
  | some native =>
    match issued : SourceCoreStageContracts.prepareSidecar
        fixture.recipe.compiled.indexed.base.plan observed.row.key with
    | .error _ => throw (IO.userError "factory original sidecar missing")
    | .ok sidecar =>
      match SourceCoreCallableContracts.descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
          (.named observed.row.key) with
      | .error error => throw (IO.userError (reprStr error))
      | .ok descriptor => return ⟨descriptor, native, present, sidecar, issued⟩

def ObservedStages.registry {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (_actual : ObservedStages fixture observed) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)

theorem ObservedStages.selected {fixture : CompiledFixture} {signature : ProgramFunctionSignature} {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    stages.registry.Closure actual.header.function
      (RecursiveStageRegistry.scope stages.sidecar [] actual.header.function) := by
  have same := RecursiveNamedPreparedStageScopes.sidecar_caller stages.issued
    (CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.record actual.prepared actual.aligned)
  rw [actual.aligned.function]
  exact RecursiveNamedPreparedStageScopes.Selected.named actual.prepared stages.sidecar stages.issued same


theorem bootstrap_zero (compiled : SourceCoreUnifiedCompilation.Compiled)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey
      (CallableIndexedOwnedPreparedBootstrapRootState.keys compiled)) :
    owner.key.capturePrefix = 0 := by
  have bound := owner.position.isLt
  change owner.position.val < 1 at bound
  have zero : owner.position.val = 0 := by omega
  simp only [CallableIndexedOwnedFunctionValues.OwnedKey.key,
    CallableIndexedOwnedPreparedBootstrapRootState.keys,
    CallableIndexedOwnedPreparedBootstrapRootState.key, zero, List.getElem_cons_zero]

theorem ActualHeader.source {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    (actual : ActualHeader fixture row) : actual.header.function.source = row.function.typedBody := by
  rw [actual.aligned.function]
  exact congrArg (fun row => row.function.typedBody) actual.prepared.same

def seed : Core.Word := Core.Word.ofNatModulo 11

def runOptions : SourceCoreExecution.RunOptions := {
  executionFuel := 100000
  inputValidationFuel := 1000
  outputValidationFuel := 1000 }

/-- Concrete public execution retains the original opened artifact, fresh
bootstrap and exact run receipt. Its scalar output is obtained from the actual public execution. -/
structure ObservedPublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) where
  artifact : SourceCoreExecution.Artifact
  opened : artifact.CompiledAt fixture.facadeCompiled
  bootstrap : SourceCoreExecution.Bootstrap artifact
  fresh : bootstrap.FreshAt
  authority : bootstrap.ExportAuthorityAt
  session : SourceCoreExecution.Session artifact
  ready : bootstrap.resume 100000 = .ready session
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start observed.row.key [.word seed, .bool true] runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt observed.row.key [.word seed, .bool true] runOptions (.ok (.succeeded completion))
  returned : completion.value = .word seed

def observePublicRun (fixture : CompiledFixture) {signature : ProgramFunctionSignature} (observed : ObservedRow fixture signature) :
    IO (ObservedPublicRun fixture observed) := do
  let opened ← fixture.facadeCompiled.openWithReceipt
  let fresh ← opened.val.bootstrapWithExportReceipt
  match ready : fresh.val.resume 100000 with
  | .error error => throw (IO.userError (reprStr error))
  | .outOfFuel _ => throw (IO.userError "factory bootstrap exhausted")
  | .ready session =>
    match started : session.start observed.row.key [.word seed, .bool true] runOptions.inputValidationFuel with
    | .error error => throw (IO.userError (reprStr error))
    | .ok checkpoint =>
      let executed ← session.runWithReceipt observed.row.key [.word seed, .bool true] runOptions
      match result : executed.val with
      | .error error => throw (IO.userError (reprStr error))
      | .ok (.failed _ _) => throw (IO.userError "factory public run failed")
      | .ok (.exportError error _) => throw (IO.userError (reprStr error))
      | .ok (.outOfFuel _) => throw (IO.userError "factory public run exhausted")
      | .ok (.succeeded completion) =>
        if returned : completion.value = .word seed then
          return ⟨opened.val, opened.property, fresh.val, fresh.property.1, fresh.property.2, session, ready,
            checkpoint, started, completion, result ▸ executed.property, returned⟩
        else throw (IO.userError "generic initial output changed")


end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectFamily
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

/-- The actual cached slot identifies one of the four prepared Source rows. -/
theorem ObservedProgram.cached_source {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : fixture.recipe.compiled.indexed.base.functions[index]? = some named) :
    CallableIndexedNamedGeneration.source named = observed.wordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.boolRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.chooseWordRow.row.function.typedBody ∨
    CallableIndexedNamedGeneration.source named = observed.chooseBoolRow.row.function.typedBody := by
  have length : fixture.recipe.compiled.indexed.base.functions.length = 4 := by
    simpa only [CallableIndexedPreparedInventories.cached_globals, List.length_map] using observed.globalsLength
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [length] at bound
  have wordBound := (List.getElem?_eq_some_iff.mp observed.wordRow.slot.selected).1
  have boolBound := (List.getElem?_eq_some_iff.mp observed.boolRow.slot.selected).1
  have chooseWordBound := (List.getElem?_eq_some_iff.mp observed.chooseWordRow.slot.selected).1
  have chooseBoolBound := (List.getElem?_eq_some_iff.mp observed.chooseBoolRow.slot.selected).1
  rw [observed.globalsLength] at wordBound boolBound chooseWordBound chooseBoolBound
  have casesIndex : index = observed.wordRow.index ∨ index = observed.boolRow.index ∨
      index = observed.chooseWordRow.index ∨ index = observed.chooseBoolRow.index := by
    have wb := observed.wordBool
    have wcw := observed.wordChooseWord
    have wcb := observed.wordChooseBool
    have bcw := observed.boolChooseWord
    have bcb := observed.boolChooseBool
    have cc := observed.chooseWordChooseBool
    omega
  rcases casesIndex with same | same | same | same
  · left
    have actualIndex := (observed.wordRow.prepared_slot wordHeader.prepared).2
    rw [same, ← actualIndex, wordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) wordHeader.prepared.same
  · right; left
    have actualIndex := (observed.boolRow.prepared_slot boolHeader.prepared).2
    rw [same, ← actualIndex, boolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) boolHeader.prepared.same
  · right; right; left
    have actualIndex := (observed.chooseWordRow.prepared_slot chooseWordHeader.prepared).2
    rw [same, ← actualIndex, chooseWordHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) chooseWordHeader.prepared.same
  · right; right; right
    have actualIndex := (observed.chooseBoolRow.prepared_slot chooseBoolHeader.prepared).2
    rw [same, ← actualIndex, chooseBoolHeader.prepared.selected] at selected
    cases Option.some.inj selected
    exact congrArg (fun row => row.function.typedBody) chooseBoolHeader.prepared.same

private theorem root_no_lambda
    {function signature generic firstParameter secondParameter firstType secondType}
    (shape : RootShape function signature generic firstParameter secondParameter firstType secondType)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : ContainsExpression function.typedBody id node)
    (form : node.form = .lambda parameters result body) : False := by
  have member := found.1
  rw [nodes, RootShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same | same
  all_goals try cases same
  · rw [shape.firstRead.form] at form; cases form
  · rw [shape.secondRead.form] at form; cases form
  · rw [shape.call.calleeForm] at form; cases form
  · rw [shape.call.form] at form; cases form

private theorem selected_no_lambda {function firstType secondType}
    (shape : SelectedShape function firstType secondType)
    (nodes : function.typedBody.nodes = shape.nodeList)
    {id node parameters result body}
    (found : ContainsExpression function.typedBody id node)
    (form : node.form = .lambda parameters result body) : False := by
  have member := found.1
  rw [nodes, SelectedShape.nodeList] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · cases same; rw [shape.read.form] at form; cases form
  · cases same

theorem CompiledFixture.no_principal (fixture : CompiledFixture)
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal fixture.recipe.compiled method) : False := by
  obtain ⟨_implementation, _method, _trait, _definition, _substitution, instantiated⟩ := principal.source_instantiation
  cases instantiated with
  | intro _ _ _ _ member _ _ _ _ _ _ _ =>
    simp only [Program.ofChecked, fixture.sameProgram, fixture.methods, List.map_nil,
      List.not_mem_nil] at member

/-- The genuine formation provenance excludes anonymous and method bodies in
this artifact. Named call support is supplied separately for all four rows. -/
def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry faults
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply False.elim
    have found := code.sourceFound
    rcases observed.cached_source wordHeader boolHeader chooseWordHeader chooseBoolHeader
        support.caller.selected with original | original | original | original
    all_goals rw [support.source.trans original] at found
    · exact False.elim (root_no_lambda observed.wordShape observed.wordNodes
        (lookupExpression?_sound found) code.sourceForm)
    · exact False.elim (root_no_lambda observed.boolShape observed.boolNodes
        (lookupExpression?_sound found) code.sourceForm)
    · exact False.elim (selected_no_lambda observed.chooseWordShape observed.chooseWordNodes
        (lookupExpression?_sound found) code.sourceForm)
    · exact False.elim (selected_no_lambda observed.chooseBoolShape observed.chooseBoolNodes
        (lookupExpression?_sound found) code.sourceForm)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectLeafSupport
/-! Both selected generic bodies are genuine specialized reads. Their metadata
and terminal support come from the actual source graph and compiler receipt. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Core Frontend SourceInference SourceSemantics CoreLowering

section Selected
variable {fixture : CompiledFixture} {row : SourceSpecialization.SpecializedFunction}
    {firstType secondType : TypeSystem.Ty}
    (shape : SelectedShape row.function firstType secondType)
    (nodes : row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row)

include nodes in
private theorem selected_expression {id : ExpressionId} {node : ExpressionNode}
    (found : row.function.typedBody.lookupExpression? id = some node) : node = shape.read.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [SelectedShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes noLocals in
theorem ActualHeader.selected_metadata (named : CallableIndexedNamedGeneration.Named) :
    CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named actual.header.function.source := by
  constructor
  · intro id _ node found
    rw [actual.source] at found
    rw [selected_expression shape nodes found]
    exact shape.read.requirements
  · intro id _ node found
    rw [actual.source] at found
    rw [selected_expression shape nodes found]
    exact shape.read.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rw [actual.source] at found
    rw [selected_expression shape nodes found, shape.read.form] at form
    cases form
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem ActualHeader.selected_syntax :
    CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.Syntax
      actual.header.function.source shape.read.node.id := by
  rw [actual.source]
  exact .leaf (.read shape.read.found shape.read.form)

include nodes noLocals in
theorem ActualHeader.selected_support
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = shape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.read.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  exact ⟨terminal, expression, CallableIndexedOwnedPreparedStagedNamedRecursiveTerminalSupport.of_actual
    terminal diagnostic receiver fixture.source_wellFormed
    (ActualHeader.selected_metadata shape nodes noLocals actual terminal.prepared.named)
    (by rw [expression]; exact ActualHeader.selected_syntax shape actual) stagePrepared point⟩
end Selected

theorem ActualHeader.chooseWord_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseWordRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.chooseWordShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact ActualHeader.selected_support observed.chooseWordShape observed.chooseWordNodes observed.noLocals actual receiver stagePrepared

theorem ActualHeader.chooseBool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.chooseBoolRow.row)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.chooseBoolShape.read.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport.NamedSupport
        actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) terminal
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  exact ActualHeader.selected_support observed.chooseBoolShape observed.chooseBoolNodes observed.noLocals actual receiver stagePrepared

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectMetadata
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (OrdinarySyntax)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Ordinary)

theorem ObservedRow.record {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) :
    SourceCompilationPlan.exactSpecialization fixture.recipe.compiled.indexed.base.plan row.row.key = .ok row.row := by
  obtain ⟨input, _same, packet, actual, _⟩ := row.issue
  have record := CallableIndexedActualNamedSourceReceipts.header_record fixture.recipe.compiled actual.header
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared,
    actual.prepared.same] at record
  exact record

private theorem retained_ordered {plan : SourceCompilationPlan.Plan}
    {row : SourceSpecialization.SpecializedFunction}
    (target : SourceCompilationPlan.exactInstantiationKey plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) = .ok row.key)
    (record : SourceCompilationPlan.exactSpecialization plan row.key = .ok row) :
    RecursiveNamedCallSelectionCertificates.Ordered plan
      (CallableNamedCanonicalOrder.retainedInstantiation row) := by
  intro key selected selectedTarget selectedRecord
  have sameKey := Except.ok.inj (target.symm.trans selectedTarget)
  subst key
  have sameRow := Except.ok.inj (record.symm.trans selectedRecord)
  subst selected
  exact List.map_reverse

theorem ObservedProgram.word_ordinary {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Ordinary fixture.recipe.compiled.indexed.base.plan observed.wordShape.call.instantiation := by
  refine ⟨?_, ?_, ?_⟩
  · rw [observed.wordShape.call.exact]
  · intro parameter replacement member
    rw [observed.wordShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.wordInstantiation]
    exact retained_ordered observed.chooseWordRow.target observed.chooseWordRow.record

theorem ObservedProgram.bool_ordinary {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) :
    Ordinary fixture.recipe.compiled.indexed.base.plan observed.boolShape.call.instantiation := by
  refine ⟨?_, ?_, ?_⟩
  · rw [observed.boolShape.call.exact]
  · intro parameter replacement member
    rw [observed.boolShape.call.exact] at member
    rcases List.mem_cons.mp member with same | member
    · rw [(Prod.mk.inj same).2]; rfl
    · have same := List.mem_singleton.mp member
      rw [(Prod.mk.inj same).2]; rfl
  · rw [observed.boolInstantiation]
    exact retained_ordered observed.chooseBoolRow.target observed.chooseBoolRow.record

section Root
variable {function : CheckedFunction} {signature generic : ProgramFunctionSignature}
  {firstParameter secondParameter : TypeSystem.TypeParameterId} {firstType secondType : TypeSystem.Ty}
  (shape : RootShape function signature generic firstParameter secondParameter firstType secondType)
  (nodes : function.typedBody.nodes = shape.nodeList)

include nodes in
theorem RootShape.expressions {id : ExpressionId} {node : ExpressionNode}
    (found : function.typedBody.lookupExpression? id = some node) :
    node = shape.firstRead.node ∨ node = shape.secondRead.node ∨
      node = shape.call.callee.node ∨ node = shape.call.value.node := by
  have present := (lookupExpression?_sound found).1
  rw [nodes] at present
  simpa only [RootShape.nodeList, List.mem_cons, List.mem_singleton,
    Node.expression.injEq, reduceCtorEq, List.not_mem_nil, false_or, or_false] using present

include nodes in
theorem RootShape.metadata {fixture : CompiledFixture}
    (named : CallableIndexedNamedGeneration.Named)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (assumptions : named.specialized.assumptions = []) :
    CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.MetadataFor
      fixture.recipe.compiled.indexed named function.typedBody
      (Ordinary fixture.recipe.compiled.indexed.base.plan) := by
  constructor
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact shape.firstRead.requirements
    · exact shape.secondRead.requirements
    · exact shape.call.callee.requirements
    · exact shape.call.value.requirements
  · intro id _ node found
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · exact shape.firstRead.coercions
    · exact shape.secondRead.coercions
    · exact shape.call.callee.coercions
    · exact shape.call.value.coercions
  · intro id _
    simp only [noLocals, List.find?_nil]
  · intro id _ node found callee ids metadata form
    rcases shape.expressions nodes found with same | same | same | same
    all_goals subst node
    · rw [shape.firstRead.form] at form; cases form
    · rw [shape.secondRead.form] at form; cases form
    · rw [shape.call.calleeForm] at form; cases form
    · rw [shape.call.form] at form; cases form
  · intro _ _ _ _ _ _ _ _
    exact assumptions
  · intro id _ node _found name binder _form
    simp only [noLocals, List.any_nil]

theorem RootShape.syntax {plan : SourceCompilationPlan.Plan}
    (ordinary : Ordinary plan shape.call.instantiation) :
    OrdinarySyntax plan function.typedBody shape.call.value.node.id := by
  refine .direct shape.call.value.found shape.call.form ordinary ?_
  intro id member
  rcases List.mem_cons.mp member with same | member
  · subst id
    exact .leaf (.read shape.firstRead.found shape.firstRead.form)
  · have same := List.mem_singleton.mp member
    subst id
    exact .leaf (.read shape.secondRead.found shape.secondRead.form)
end Root
end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectRootSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Ordinary)

/-- The original nonempty instantiation remains attached to the actual
terminal callback and the complete inventory that issued its selected callee. -/
theorem ActualHeader.root_support {fixture : CompiledFixture}
    {signature generic : ProgramFunctionSignature}
    {firstParameter secondParameter : TypeSystem.TypeParameterId}
    {firstType secondType : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : RootShape row.row.function signature generic firstParameter secondParameter firstType secondType)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (ordinary : Ordinary fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    (actual : ActualHeader fixture row.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = shape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.call.value.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  have same : terminal.prepared.named.specialized = row.row :=
    (congrArg (·.specialized) (terminal.aligned.named.symm.trans actual.aligned.named)).trans actual.prepared.same
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (Ordinary fixture.recipe.compiled.indexed.base.plan) := by
    rw [actual.source]
    exact .of_ordinary (shape.metadata nodes terminal.prepared.named noLocals (by rw [same]; exact row.assumptions))
  exact ⟨terminal, expression,
    CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual_native_sites
      terminal diagnostic receiver fixture.source_wellFormed (fun _ witness => witness) metadata
      (by rw [expression, actual.source]; exact shape.syntax ordinary)
      rows complete (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

theorem ActualHeader.word_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.wordRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.wordShape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) :=
  actual.root_support observed.wordRow.toObservedRow observed.wordShape observed.wordNodes
    observed.noLocals observed.word_ordinary rows complete receiver stagePrepared

theorem ActualHeader.bool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.boolRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.boolShape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) :=
  actual.root_support observed.boolRow.toObservedRow observed.boolShape observed.boolNodes
    observed.noLocals observed.bool_ordinary rows complete receiver stagePrepared

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectRuntime
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics

structure ObservedCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) where
  checkpoint : SourceCoreExecution.Checkpoint artifact
  started : session.start key arguments runOptions.inputValidationFuel = .ok checkpoint
  completion : SourceCoreExecution.Completion artifact
  executed : session.RunAt key arguments runOptions (.ok (.succeeded completion))
  returned : completion.value = expected

def observeCall {artifact : SourceCoreExecution.Artifact}
    (session : SourceCoreExecution.Session artifact) (key : SourceCoreIndexedSession.Key)
    (arguments : List SourceCorePublicValues.Value) (expected : SourceCorePublicValues.Value) :
    IO (ObservedCall session key arguments expected) := do
  match started : session.start key arguments runOptions.inputValidationFuel with
  | .error error => throw (IO.userError (reprStr error))
  | .ok checkpoint =>
    let executed ← session.runWithReceipt key arguments runOptions
    match result : executed.val with
    | .error error => throw (IO.userError (reprStr error))
    | .ok (.failed _ _) => throw (IO.userError "generic direct call failed")
    | .ok (.exportError error _) => throw (IO.userError (reprStr error))
    | .ok (.outOfFuel _) => throw (IO.userError "generic direct call exhausted")
    | .ok (.succeeded completion) =>
      if returned : completion.value = expected then
        return ⟨checkpoint, started, completion, result ▸ executed.property, returned⟩
      else throw (IO.userError "generic direct call output changed")

structure ObservedSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  first : ObservedPublicRun fixture observed.wordRow.toObservedRow
  second : ObservedCall first.completion.session observed.boolRow.row.key
    [.bool false, .word (Core.Word.ofNatModulo 22)] (.bool false)
  third : ObservedCall second.completion.session observed.wordRow.row.key
    [.word (Core.Word.ofNatModulo 33), .bool false] (.word (Core.Word.ofNatModulo 33))
  fourth : ObservedCall third.completion.session observed.boolRow.row.key
    [.bool true, .word (Core.Word.ofNatModulo 44)] (.bool true)

def observeSequence (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    IO (ObservedSequence fixture observed) := do
  let first ← observePublicRun fixture observed.wordRow.toObservedRow
  let second ← observeCall first.completion.session observed.boolRow.row.key
    [.bool false, .word (Core.Word.ofNatModulo 22)] (.bool false)
  let third ← observeCall second.completion.session observed.wordRow.row.key
    [.word (Core.Word.ofNatModulo 33), .bool false] (.word (Core.Word.ofNatModulo 33))
  let fourth ← observeCall third.completion.session observed.boolRow.row.key
    [.bool true, .word (Core.Word.ofNatModulo 44)] (.bool true)
  pure ⟨first, second, third, fourth⟩
end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicRootMeaning (RootSelection)
open RecursiveNamedPublicHistoryFrontdoor (Started)

theorem ActualHeader.key {fixture : CompiledFixture}
    {row : SourceSpecialization.SpecializedFunction} (actual : ActualHeader fixture row) :
    actual.header.named.signature.key = row.key := by
  rw [actual.aligned.named]
  exact RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared

theorem ObservedRow.keys_ne {fixture : CompiledFixture} {leftSignature rightSignature : ProgramFunctionSignature}
    (left : ObservedRow fixture leftSignature) (right : ObservedRow fixture rightSignature)
    (distinct : left.index ≠ right.index) : left.row.key ≠ right.row.key := by
  intro same
  have globals : left.global.key = right.global.key := left.globalKey.trans (same.trans right.globalKey.symm)
  exact distinct (left.slot.unique right.slot globals).2

private theorem selected_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {root : SourceCoreIndexedSession.Root compiled}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (selected : RootSelection (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers root header) :
    header.named.signature.key = root.key := by
  obtain ⟨_, entry, _, shape, found⟩ := selected
  obtain ⟨named, index, first, namedKey, rootKey, _⟩ := shape
  obtain ⟨namedEq, _⟩ := Prod.mk.inj (Option.some.inj (found.symm.trans first))
  rw [namedEq]
  exact namedKey.trans rootKey.symm

theorem selected_word_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] root header)
    (key : root.key = observed.wordRow.row.key) : header = wordHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, boolHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.boolRow.toObservedRow observed.wordBool) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, chooseWordHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.chooseWordRow observed.wordChooseWord) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, chooseBoolHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.chooseBoolRow observed.wordChooseBool) headerKey.symm)

theorem selected_bool_root {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {root : SourceCoreIndexedSession.Root fixture.recipe.compiled}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    (selected : RootSelection (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      [wordHeader.header, boolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] root header)
    (key : root.key = observed.boolRow.row.key) : header = boolHeader.header := by
  have member : header ∈ [wordHeader.header, boolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] := selected.member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same | same
  · have headerKey := (selected_key selected).trans key
    rw [same, wordHeader.key] at headerKey
    exact False.elim ((observed.wordRow.keys_ne observed.boolRow.toObservedRow observed.wordBool) headerKey)
  · exact same
  · have headerKey := (selected_key selected).trans key
    rw [same, chooseWordHeader.key] at headerKey
    exact False.elim ((observed.boolRow.keys_ne observed.chooseWordRow observed.boolChooseWord) headerKey.symm)
  · have headerKey := (selected_key selected).trans key
    rw [same, chooseBoolHeader.key] at headerKey
    exact False.elim ((observed.boolRow.keys_ne observed.chooseBoolRow observed.boolChooseBool) headerKey.symm)

private theorem cast_key {left right : SourceCoreUnifiedCompilation.Compiled}
    (same : left = right) (root : SourceCoreIndexedSession.Root left) :
    (same ▸ root).key = root.key := by
  cases same
  rfl

private theorem started_key {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    {recipe : SourceCoreIndexedSession.Recipe}
    {prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe}
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}
    (request : Started headers prepared publicCheckpoint session key arguments fuel world store) :
    request.root.key = key := by
  have keyEq := of_decide_eq_true (List.find?_some
    (p := fun root : SourceCoreIndexedSession.Root recipe.compiled => decide (root.key = key))
    request.started.selected)
  exact (cast_key (SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm request.root).symm.trans keyEq

section StartedSelection
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordHeader : ActualHeader fixture observed.wordRow.row)
    (boolHeader : ActualHeader fixture observed.boolRow.row)
    (chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row)
    (chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {nativeArtifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session nativeArtifact}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {world : Core.StoreTyping} {store : Core.Store}

theorem selected_word_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, chooseWordHeader.header, chooseBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.wordRow.row.key arguments fuel world store) : request.header = wordHeader.header := by
  subst headers
  exact selected_word_root wordHeader boolHeader chooseWordHeader chooseBoolHeader request.selected (started_key request)

theorem selected_bool_at
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    (headerList : headers = [wordHeader.header, boolHeader.header, chooseWordHeader.header, chooseBoolHeader.header])
    (request : Started headers fixture.recipePrepared publicCheckpoint session
      observed.boolRow.row.key arguments fuel world store) : request.header = boolHeader.header := by
  subst headers
  exact selected_bool_root wordHeader boolHeader chooseWordHeader chooseBoolHeader request.selected (started_key request)
end StartedSelection

theorem ActualHeader.word_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.word, .bool] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.wordShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.wordShape.firstScheme, observed.wordShape.secondScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.word_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.types = [.word, .bool] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.word_input_types

theorem ActualHeader.word_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.function.resultType = .word := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.wordResultType

theorem ActualHeader.word_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.wordRow.row) : actual.header.output = .word := by
  have projected := actual.aligned.projection
  rw [actual.word_result_type] at projected
  exact (Except.ok.inj projected).symm

theorem ActualHeader.bool_input_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) :
    actual.header.bindings.map (fun binding => binding.1.scheme.body) = [.bool, .word] := by
  have inputs := congrArg (fun binders => binders.map (fun binder => binder.scheme.body)) actual.header.inputs
  rw [actual.source, observed.boolShape.inputs] at inputs
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    observed.boolShape.firstScheme, observed.boolShape.secondScheme, TypeSystem.Scheme.mono] using inputs.symm

theorem ActualHeader.bool_types {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.types = [.bool, .word] := by
  have types := Dynamic.MonoBindersExtend.bodyTypes_eq actual.header.extended
  rw [actual.header.parameters] at types
  simp only [List.map_map, Function.comp_def] at types
  exact types.symm.trans actual.bool_input_types

theorem ActualHeader.bool_result_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.function.resultType = .bool := by
  rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
  exact observed.boolResultType

theorem ActualHeader.bool_output {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.boolRow.row) : actual.header.output = .bool := by
  have projected := actual.aligned.projection
  rw [actual.bool_result_type] at projected
  exact (Except.ok.inj projected).symm

def ObservedStages.descriptor_at {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature} (stages : ObservedStages fixture observed)
    (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.key]
  exact stages.descriptor

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectSupports
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body of_terminal)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  wordInput : Input fixture.recipe.compiled
  boolInput : Input fixture.recipe.compiled
  chooseWordInput : Input fixture.recipe.compiled
  chooseBoolInput : Input fixture.recipe.compiled
  wordRow : wordInput.row = observed.wordRow.row
  boolRow : boolInput.row = observed.boolRow.row
  chooseWordRow : chooseWordInput.row = observed.chooseWordRow.row
  chooseBoolRow : chooseBoolInput.row = observed.chooseBoolRow.row
  wordPacket : Issued wordInput
  boolPacket : Issued boolInput
  chooseWordPacket : Issued chooseWordInput
  chooseBoolPacket : Issued chooseBoolInput
  wordHeader : ActualHeader fixture observed.wordRow.row
  boolHeader : ActualHeader fixture observed.boolRow.row
  chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row
  chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row
  wordEq : wordHeader.header = wordPacket.header
  boolEq : boolHeader.header = boolPacket.header
  chooseWordEq : chooseWordHeader.header = chooseWordPacket.header
  chooseBoolEq : chooseBoolHeader.header = chooseBoolPacket.header
  rows : Inventory [wordInput, boolInput, chooseWordInput, chooseBoolInput]
  rowsEq : rows = (.cons wordPacket (.cons boolPacket (.cons chooseWordPacket (.cons chooseBoolPacket  .nil))))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([wordInput, boolInput, chooseWordInput, chooseBoolInput].map (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  wordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named wordHeader.header.named.signature.key)
  boolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named boolHeader.header.named.signature.key)
  chooseWordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseWordHeader.header.named.signature.key)
  chooseBoolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseBoolHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.wordHeader.header, support.boolHeader.header, support.chooseWordHeader.header, support.chooseBoolHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.wordEq, support.boolEq, support.chooseWordEq, support.chooseBoolEq]

private def selectFour {compiled : SourceCoreUnifiedCompilation.Compiled}
    {word bool chooseWord chooseBool : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (wordBool : word.slot ≠ bool.slot)
    (wordChooseWord : word.slot ≠ chooseWord.slot)
    (wordChooseBool : word.slot ≠ chooseBool.slot)
    (boolChooseWord : bool.slot ≠ chooseWord.slot)
    (boolChooseBool : bool.slot ≠ chooseBool.slot)
    (chooseWordChooseBool : chooseWord.slot ≠ chooseBool.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (wordValue : property word)
    (boolValue : property bool)
    (chooseWordValue : property chooseWord)
    (chooseBoolValue : property chooseBool)
    : ∀ header, header ∈ [word, bool, chooseWord, chooseBool] → property header := by
  intro header member
  if wordSlot : header.slot = word.slot then
    have same : header = word := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact same
      · exact False.elim (wordBool (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordChooseWord (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordChooseBool (wordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ wordValue
  else if boolSlot : header.slot = bool.slot then
    have same : header = bool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (boolChooseWord (boolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (boolChooseBool (boolSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ boolValue
  else if chooseWordSlot : header.slot = chooseWord.slot then
    have same : header = chooseWord := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (chooseWordChooseBool (chooseWordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ chooseWordValue
  else
    have same : header = chooseBool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact False.elim (chooseWordSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ chooseBoolValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨wordInput, boolInput, chooseWordInput, chooseBoolInput, wordRow, boolRow, chooseWordRow, chooseBoolRow, wordPacket, boolPacket, chooseWordPacket, chooseBoolPacket, wordHeader, boolHeader, chooseWordHeader, chooseBoolHeader, wordEq, boolEq, chooseWordEq, chooseBoolEq, complete⟩ := observed.inventory
  let rows : Inventory [wordInput, boolInput, chooseWordInput, chooseBoolInput] := (.cons wordPacket (.cons boolPacket (.cons chooseWordPacket (.cons chooseBoolPacket  .nil))))
  have headerList : headers rows = [wordHeader.header, boolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] := by
    simp only [rows, headers, wordEq, boolEq, chooseWordEq, chooseBoolEq]
  have wordIndex : wordHeader.header.slot = observed.wordRow.index :=
    wordHeader.aligned.slot.trans (observed.wordRow.prepared_slot wordHeader.prepared).2
  have wordInputIndex : wordHeader.header.slot = wordInput.prepared.index := by
    rw [wordEq]; exact wordPacket.aligned.slot
  have boolIndex : boolHeader.header.slot = observed.boolRow.index :=
    boolHeader.aligned.slot.trans (observed.boolRow.prepared_slot boolHeader.prepared).2
  have boolInputIndex : boolHeader.header.slot = boolInput.prepared.index := by
    rw [boolEq]; exact boolPacket.aligned.slot
  have chooseWordIndex : chooseWordHeader.header.slot = observed.chooseWordRow.index :=
    chooseWordHeader.aligned.slot.trans (observed.chooseWordRow.prepared_slot chooseWordHeader.prepared).2
  have chooseWordInputIndex : chooseWordHeader.header.slot = chooseWordInput.prepared.index := by
    rw [chooseWordEq]; exact chooseWordPacket.aligned.slot
  have chooseBoolIndex : chooseBoolHeader.header.slot = observed.chooseBoolRow.index :=
    chooseBoolHeader.aligned.slot.trans (observed.chooseBoolRow.prepared_slot chooseBoolHeader.prepared).2
  have chooseBoolInputIndex : chooseBoolHeader.header.slot = chooseBoolInput.prepared.index := by
    rw [chooseBoolEq]; exact chooseBoolPacket.aligned.slot
  have wordBool : wordHeader.header.slot ≠ boolHeader.header.slot := by
    rw [wordIndex, boolIndex]; exact observed.wordBool
  have wordBoolInput : wordInput.prepared.index ≠ boolInput.prepared.index := by
    rw [← wordInputIndex, ← boolInputIndex]; exact wordBool
  have wordChooseWord : wordHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [wordIndex, chooseWordIndex]; exact observed.wordChooseWord
  have wordChooseWordInput : wordInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← wordInputIndex, ← chooseWordInputIndex]; exact wordChooseWord
  have wordChooseBool : wordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [wordIndex, chooseBoolIndex]; exact observed.wordChooseBool
  have wordChooseBoolInput : wordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← wordInputIndex, ← chooseBoolInputIndex]; exact wordChooseBool
  have boolChooseWord : boolHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [boolIndex, chooseWordIndex]; exact observed.boolChooseWord
  have boolChooseWordInput : boolInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← boolInputIndex, ← chooseWordInputIndex]; exact boolChooseWord
  have boolChooseBool : boolHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [boolIndex, chooseBoolIndex]; exact observed.boolChooseBool
  have boolChooseBoolInput : boolInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← boolInputIndex, ← chooseBoolInputIndex]; exact boolChooseBool
  have chooseWordChooseBool : chooseWordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [chooseWordIndex, chooseBoolIndex]; exact observed.chooseWordChooseBool
  have chooseWordChooseBoolInput : chooseWordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← chooseWordInputIndex, ← chooseBoolInputIndex]; exact chooseWordChooseBool
  obtain ⟨wordTerminal, _wordExpression, ⟨wordSupport⟩⟩ :=
    wordHeader.word_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨boolTerminal, _boolExpression, ⟨boolSupport⟩⟩ :=
    boolHeader.bool_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨chooseWordTerminal, _chooseWordExpression, ⟨chooseWordSupport⟩⟩ :=
    chooseWordHeader.chooseWord_support observed receiver (actualStagePrepared fixture)
  obtain ⟨chooseBoolTerminal, _chooseBoolExpression, ⟨chooseBoolSupport⟩⟩ :=
    chooseBoolHeader.chooseBool_support observed receiver (actualStagePrepared fixture)
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectFour wordBool wordChooseWord wordChooseBool boolChooseWord boolChooseBool chooseWordChooseBool property
      ⟨of_terminal wordTerminal, .canonical wordSupport⟩ ⟨of_terminal boolTerminal, .canonical boolSupport⟩ ⟨of_terminal chooseWordTerminal, .recursive chooseWordSupport⟩ ⟨of_terminal chooseBoolTerminal, .recursive chooseBoolSupport⟩ header (headerList ▸ member)
  exact ⟨{
    wordInput := wordInput
    boolInput := boolInput
    chooseWordInput := chooseWordInput
    chooseBoolInput := chooseBoolInput
    wordRow := wordRow
    boolRow := boolRow
    chooseWordRow := chooseWordRow
    chooseBoolRow := chooseBoolRow
    wordPacket := wordPacket
    boolPacket := boolPacket
    chooseWordPacket := chooseWordPacket
    chooseBoolPacket := chooseBoolPacket
    wordHeader := wordHeader
    boolHeader := boolHeader
    chooseWordHeader := chooseWordHeader
    chooseBoolHeader := chooseBoolHeader
    wordEq := wordEq
    boolEq := boolEq
    chooseWordEq := chooseWordEq
    chooseBoolEq := chooseBoolEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [wordBoolInput, wordChooseWordInput, wordChooseBoolInput, boolChooseWordInput, boolChooseBoolInput, chooseWordChooseBoolInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family wordHeader boolHeader chooseWordHeader chooseBoolHeader rows (actualStagePrepared fixture) association
    wordDescriptor := wordStages.descriptor_at wordHeader
    boolDescriptor := boolStages.descriptor_at boolHeader
    chooseWordDescriptor := chooseWordStages.descriptor_at chooseWordHeader
    chooseBoolDescriptor := chooseBoolStages.descriptor_at chooseBoolHeader }⟩

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectCommon
/-! Genuine initial diagnostics and current retained public sessions. No
independent native execution is used to construct the semantic receiver. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open RecursiveNamedPublicFunctionHistory (Entry)

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

/-- Any later actual public startup on this compiled artifact recovers its
same recipe, exact indexed session, checkpoint, input encoding and store. -/
theorem CompiledFixture.actual_start (fixture : CompiledFixture)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    (opened : publicArtifact.CompiledAt fixture.facadeCompiled)
    (started : publicSession.start key arguments fuel = .ok publicCheckpoint) :
    ∃ (artifact : SourceCoreIndexedSession.Artifact)
      (session : SourceCoreIndexedSession.Session artifact)
      (checkpoint : SourceCoreIndexedSession.Checkpoint artifact)
      (root : SourceCoreIndexedSession.Root fixture.recipe.compiled)
      (world : Core.StoreTyping) (store : Core.Store) (native : Core.Environment)
      (encodedValues : SourceCoreCompatibleValues.Context),
      publicArtifact.IndexedAt fixture.facadeCompiled fixture.recipe artifact ∧
      SourceCoreIndexedSession.Recipe.prepare fixture.recipe.compiled = .ok fixture.recipe ∧
      publicSession.IndexedAt session ∧ publicCheckpoint.IndexedAt checkpoint ∧
      RecursiveNamedPublicStartMeaning.StartAt session key arguments fuel
        checkpoint fixture.recipe root world store native encodedValues := by
  obtain ⟨recipe, artifact, session, checkpoint, root, world, store, native, encodedValues,
      atArtifact, prepared, _program, sessionAt, checkpointAt, startReceipt⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start fixture.accepted opened started
  have same := recipe_unique atArtifact.compiled_recipe fixture.issued
  cases same
  exact ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
    atArtifact, prepared, sessionAt, checkpointAt, startReceipt⟩


structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.wordRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


abbrev PublicSupports {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (receiver : ObservedReceiver fixture observed) :=
  StaticSupportPackage fixture observed receiver.completion.result.context.registry receiver.completion

def PublicSupports.functions {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :=
  CallableIndexedOwnedContextualCellOrigins.functions (headers support.rows)
    (keys fixture.recipe.compiled) receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics) observed.profile

theorem PublicSupports.observations {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    CompatibleEquality.FunctionObservations fixture.recipe.compiled.compatible.checked.catalog
      support.functions (CallableIndexedLambdaValues.Identity fixture.recipe.compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ receiver.completion.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile (registry := metadata)
    (CallableIndexedOwnedContextualCellOrigins.functions_include_general observed.profile origin)

structure RetainedState {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {publicArtifact : SourceCoreExecution.Artifact} (publicSession : SourceCoreExecution.Session publicArtifact)
    (entries : List Entry) where
  artifact : SourceCoreIndexedSession.Artifact
  session : SourceCoreIndexedSession.Session artifact
  mapping : GeneralHeap.LocationMap
  world : Core.StoreTyping
  heap : Dynamic.Heap
  store : Core.Store
  caller : RecursiveNamedPublicFunctionHistory.Caller (headers support.rows)
    (keys fixture.recipe.compiled) mapping world heap store
  atSession : publicSession.IndexedAt session
  atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact fixture.recipe
  receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    receiving.entry receiving.result.context.registry receiving.result.extension receiving.result.diagnostics
  extension : SourceCoreRawMetadata.Extends receiver.completion.result.context.registry receiving.result.context.registry
  registry : session.RegistryAt receiving.result.context.registry
  history : RecursiveNamedPublicFunctionHistory.History (headers support.rows)
    (keys fixture.recipe.compiled) support.functions receiving.result.context.registry
    support.wordHeader.header session mapping world heap store caller entries

def SourceCall {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (arguments : List Dynamic.Value)
    (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) : Prop :=
  ∃ rawD function size,
    CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function ∧
    Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) size invocation
      support.wordHeader.header.function.context before (.global function) arguments outcome after

theorem word_bool_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (word : Core.Word) (flag : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.word, .bool]
      [.word word, .bool flag] [.word word, .bool flag] := by
  exact .cons (.data
    ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
    ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩)
    (.cons (.data
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
      ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩) .nil)

theorem bool_word_inputs {entries : List Entry} {context : SourceSemantics.Context}
    (flag : Bool) (word : Core.Word) :
    RecursiveNamedPublicFunctionHistoryInputs.Inputs entries context [.bool, .word]
      [.bool flag, .word word] [.bool flag, .word word] := by
  exact .cons (.data
    ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
    ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
    (.cons (.data
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩
      ⟨.word word, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word word⟩) .nil)

theorem word_bool_simple (word : Core.Word) (flag : Bool) :
    ∀ value ∈ ([.word word, .bool flag] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .word word
  · exact .bool flag

theorem bool_word_simple (flag : Bool) (word : Core.Word) :
    ∀ value ∈ ([.bool flag, .word word] : List SourceCorePublicValues.Value),
      SourceCoreIndexedSession.SimplePublic value := by
  intro value member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .bool flag
  · exact .word word

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectSeed
/-! The initial generic direct call derives its Source trace, Word result and reusable
empty history from actual bootstrap, input encoding and public completion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem first_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed}
    (support : PublicSupports receiver) (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ state : RetainedState support first.completion.session [],
      SourceCall support support.wordHeader.header
        (RecursiveStageRegistry.scope stages.sidecar [] support.wordHeader.header.function)
        ⟨[]⟩ [.word seed, .bool true] (.value (.word seed)) state.heap := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  have ready : first.bootstrap.ReadyAt 100000 first.session := .single first.ready
  obtain ⟨_bootstrap, initialized, _value, _initialStore, _atBootstrap, initial,
      initializedAt, _done, booted⟩ := ready.indexed opened first.fresh
  have same : initialized = session := initializedAt.unique sessionAt
  subst initialized
  have startupRegistry : encodedValues.registry = fixture.recipe.compiled.compatible.checked.staticRegistry := by
    apply started.simple_registry (booted.registry_at initial)
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word seed
    · exact .bool true
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.wordHeader.header := by
    apply selected_word_root support.wordHeader support.boolHeader support.chooseWordHeader support.chooseBoolHeader
      (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.wordHeader.header.function.context
      (support.wordHeader.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word seed, .bool true] [.word seed, .bool true] := by
    rw [support.wordHeader.word_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩))
      (.cons (.leaf (.data
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩)) .nil)
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiver.completion.result.context.registry := by
    rw [startupRegistry]
    exact receiver.completion.result.extension
  have sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt support.wordHeader.header support.wordInput.prepared.available
      (CallableNamedReversal.global (CallableNamedMetadata.global support.wordPacket.header.named.specialized support.wordInput.prepared.available)) := by
    rw [support.wordEq]
    exact support.wordPacket.sourceAt
  obtain ⟨caller, actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      returnedCaller, added, handles, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedHistoryPublicSeed.public_run_succeeded_collects
      (inputs := [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (extension := receiver.completion.result.extension)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := first.fresh) (ready := .single first.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl first.session) (atSession := sessionAt)
      (atCheckpoint := checkpointAt) (started := started) (inputReceipts := inputs)
      (metadata := metadata) (sourceAt := sourceAt)
      (invocation := RecursiveStageRegistry.scope stages.sidecar [] support.wordHeader.header.function)
      first.started first.executed .skip support.wordDescriptor
  have empty : added = [] := List.map_eq_nil_iff.mp handles
  subst added
  have returnedRegistry := started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [resultType, support.wordHeader.word_result_type] at requested
  have outcomeValue := RecursiveNamedPublicWordResultMeaning.result_word succeeded requested
    (valueEq.symm.trans first.returned) support.wordHeader.word_output result
  let state : RetainedState support first.completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := returnedCaller
    atSession := returnedAt
    atRecipe := started.recipe_eq
    receiving := receiver.completion
    issued := receiver.issued
    extension := .refl _
    registry := receiver.registry.symm ▸ returnedRegistry
    history := retained }
  exact ⟨state, support.wordInput.prepared.available, _, sourceSize, sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectStep
/-! Actual named calls with Word or Bool results continue the same retained session and Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

theorem RetainedState.finished_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ after : RetainedState support call.completion.session entries,
      SourceCall support request.header invocation state.heap arguments
        (.value scalar.source) after.heap := by
  have registry := request.started.simple_registry state.registry simple
  have metadata : SourceCoreRawMetadata.Extends request.encodedValues.registry state.receiving.result.context.registry := by
    rw [registry]; exact .refl _
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨actual, generation, native, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result,
      reached, _related, retained⟩ :=
    CallableIndexedOwnedPreparedStagedHistoryPublicContinuations.public_run_succeeded_retains
      (inputs := [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (extension := state.receiving.result.extension) (semantic := semantic)
      (family := support.family) (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (metadata := metadata) (sourceAt := request.sourceAt)
      (invocation := invocation) call.started call.executed descriptor
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, rawType] at requested
  have represented := result.2.1
  rw [nativeType] at represented
  have outcomeValue := scalar.source_value succeeded requested (valueEq.symm.trans call.returned) represented
  have returnedRegistry := request.started.returned_registry succeeded
  rw [registry] at returnedRegistry
  let next : RetainedState support call.completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := returnedAt
    atRecipe := state.atRecipe
    receiving := state.receiving
    issued := state.issued
    extension := state.extension
    registry := returnedRegistry
    history := retained }
  exact ⟨next, request.rawD, request.function, sourceSize, request.sourceAt, outcomeValue ▸ trace⟩

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectInitialForward
/-! The independent generic direct trace determines both public fuel bounds at its
original checkpoint. Every sufficient resume returns Word11 and the same heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering

/-- The initial entry exports its genuine raw result type and returns the exact
Source heap in a reusable session at every sufficient pair of fuel budgets. -/
def InitialForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome first.artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      first.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion first.artifact,
        outcome = .succeeded completion ∧
        completion.value = .word seed ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session [], returned.heap = after

theorem forward_initial {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support support.wordHeader.header invocation ⟨[]⟩ [.word seed, .bool true] (.value (.word seed)) after) :
    InitialForwardAt support first after := by
  obtain ⟨artifact, session, checkpoint, root, world, store, native, encodedValues,
      opened, prepared, sessionAt, checkpointAt, started⟩ := fixture.actual_start first.opened first.started
  obtain ⟨selectedHeader, selected⟩ := started.selection prepared support.complete
  have selectedEq : selectedHeader = support.wordHeader.header := by
    apply selected_word_root support.wordHeader support.boolHeader support.chooseWordHeader support.chooseBoolHeader
      (root := root) (header := selectedHeader)
    · exact support.header_list ▸ selected
    · exact of_decide_eq_true (List.find?_some (p := fun candidate : SourceCoreIndexedSession.Root fixture.recipe.compiled =>
        decide (candidate.key = observed.wordRow.row.key)) started.selected)
  subst selectedHeader
  have inputs : RecursiveNamedPublicNestedInputs.Inputs support.rows session support.wordHeader.header.function.context
      (support.wordHeader.header.bindings.map (fun binding => binding.1.scheme.body))
      [.word seed, .bool true] [.word seed, .bool true] := by
    rw [support.wordHeader.word_input_types]
    exact .cons (.leaf (.data
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩))
      (.cons (.leaf (.data
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩
        ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩)) .nil)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _caller, _capture,
      _payload, _finalStore, _finalMap, _finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, _fullResult, publicEnough⟩ :=
    CallableIndexedOwnedPreparedStagedInitializedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows) (distinct := support.distinct)
      (stagePrepared := actualStagePrepared fixture) (receiver := receiver.issued)
      (profile := observed.profile) (bodyRegistry := receiver.completion.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
      (observations := support.observations) (baseRegistry := receiver.registry)
      (semantic := by intro reason token represented; exact represented)
      (family := support.family) (namedTerminals := support.terminals)
      (namedSupport := support.supports) (wellFormed := fixture.source_wellFormed)
      (prepared := prepared) (selected := selected) (opened := opened)
      (fresh := first.fresh) (ready := .single first.ready) (authority := first.authority)
      (atSession := sessionAt) (atCheckpoint := checkpointAt) (started := started)
      (inputReceipts := inputs) (sourceAt := sourceAt) applied
  have atRecipe : artifact.RecipeAt fixture.recipe := by
    cases artifact
    exact started.recipe_eq
  have requested := started.original.result_type_at atRecipe started.selected
  have rawResult := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).2
  rw [rawResult, support.wordHeader.word_result_type] at requested
  have nativeWord : _payload = .word seed := by
    have represented := _fullResult.2.1
    rw [support.wordHeader.word_output] at represented
    cases represented with
    | value related =>
      obtain ⟨word, same, native⟩ := CompatibleExpressionPrimitives.word_fields related
      exact native.trans (congrArg Core.Value.word (Dynamic.Value.word.inj same).symm)
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, ready⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session [] := {
    artifact := artifact
    session := actual.session
    mapping := _finalMap
    world := _finalWorld
    heap := after
    store := _finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := started.recipe_eq
    receiving := receiving
    issued := issued
    extension := extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans ((nativeWord ▸ exported).word_value requested),
    actualAt.2.2.2.exportsReady_iff.mpr ready, returned, rfl⟩


end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectPublicExecution
/-! Both actual instantiations of choose remain distinct in the compiler
inventory. Four public calls use their exact successive sessions and Source heaps. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure CallMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (before : RetainedState support session [])
    (header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (arguments : List Dynamic.Value) (invocation : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.rows) fixture.recipePrepared
    call.checkpoint before.session key publicArguments runOptions.inputValidationFuel before.world before.store
  headerEq : request.header = header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : RetainedState support call.completion.session []
  trace : SourceCall support header invocation before.heap arguments (.value scalar.source) after.heap

theorem RetainedState.word_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session [])
    (word : Core.Word) (flag : Bool)
    (call : ObservedCall session observed.wordRow.row.key [.word word, .bool flag] (.word word))
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.wordHeader.header (.word word) call [.word word, .bool flag] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]
    support.rows support.complete state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.wordHeader.header :=
    selected_word_at support.wordHeader support.boolHeader support.chooseWordHeader support.chooseBoolHeader
      support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word word, .bool flag] [.word word, .bool flag] := by
    rw [selected, support.wordHeader.word_input_types]
    exact word_bool_inputs word flag
  have raw : request.header.function.resultType = (ScalarOutput.word word).sourceType := by
    rw [selected, support.wordHeader.word_result_type]; rfl
  have native : request.header.output = (ScalarOutput.word word).nativeType := by
    rw [selected, support.wordHeader.word_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact stages.descriptor_at support.wordHeader
  obtain ⟨after, trace⟩ := state.finished_call (.word word) call request inputs
    (word_bool_simple word flag) raw native descriptor invocation
  exact ⟨⟨request, selected, inputs, raw, native, after, by rw [← selected]; exact trace⟩⟩

theorem RetainedState.bool_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (state : RetainedState support session [])
    (flag : Bool) (word : Core.Word)
    (call : ObservedCall session observed.boolRow.row.key [.bool flag, .word word] (.bool flag))
    (stages : ObservedStages fixture observed.boolRow.toObservedRow)
    (invocation : Staging.Recursive.Scope) :
    Nonempty (CallMeaning state support.boolHeader.header (.bool flag) call [.bool flag, .word word] invocation) := by
  obtain ⟨request⟩ := RecursiveNamedPublicHistoryFrontdoor.recover_start
    fixture.recipePrepared [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]
    support.rows support.complete state.atRecipe state.history.current.1 state.atSession call.started
  have selected : request.header = support.boolHeader.header :=
    selected_bool_at support.wordHeader support.boolHeader support.chooseWordHeader support.chooseBoolHeader
      support.header_list request
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs [] request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool flag, .word word] [.bool flag, .word word] := by
    rw [selected, support.boolHeader.bool_input_types]
    exact bool_word_inputs flag word
  have raw : request.header.function.resultType = (ScalarOutput.bool flag).sourceType := by
    rw [selected, support.boolHeader.bool_result_type]; rfl
  have native : request.header.output = (ScalarOutput.bool flag).nativeType := by
    rw [selected, support.boolHeader.bool_output]; rfl
  have descriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named request.header.named.signature.key) := by
    rw [selected]
    exact stages.descriptor_at support.boolHeader
  obtain ⟨after, trace⟩ := state.finished_call (.bool flag) call request inputs
    (bool_word_simple flag word) raw native descriptor invocation
  exact ⟨⟨request, selected, inputs, raw, native, after, by rw [← selected]; exact trace⟩⟩

structure SequenceWitness {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) where
  support : PublicSupports receiver
  initial : RetainedState support sequence.first.completion.session []
  firstTrace : SourceCall support support.wordHeader.header
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
    ⟨[]⟩ [.word seed, .bool true] (.value (.word seed)) initial.heap
  secondMeaning : CallMeaning initial support.boolHeader.header (.bool false) sequence.second
    [.bool false, .word (Core.Word.ofNatModulo 22)]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  thirdMeaning : CallMeaning secondMeaning.after support.wordHeader.header (.word (Core.Word.ofNatModulo 33)) sequence.third
    [.word (Core.Word.ofNatModulo 33), .bool false]
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  fourthMeaning : CallMeaning thirdMeaning.after support.boolHeader.header (.bool true) sequence.fourth
    [.bool true, .word (Core.Word.ofNatModulo 44)]
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)

theorem sequence_meaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨support⟩ := static_supports fixture observed wordStages boolStages chooseWordStages chooseBoolStages
    receiver.completion.result.context.registry receiver.issued
  obtain ⟨initial, firstTrace⟩ := first_meaning support wordStages sequence.first
  obtain ⟨second⟩ := initial.bool_meaning false (Core.Word.ofNatModulo 22) sequence.second boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  obtain ⟨third⟩ := second.after.word_meaning (Core.Word.ofNatModulo 33) false sequence.third wordStages
    (RecursiveStageRegistry.scope wordStages.sidecar [] support.wordHeader.header.function)
  obtain ⟨fourth⟩ := third.after.bool_meaning true (Core.Word.ofNatModulo 44) sequence.fourth boolStages
    (RecursiveStageRegistry.scope boolStages.sidecar [] support.boolHeader.header.function)
  exact ⟨⟨support, initial, firstTrace, second, third, fourth⟩⟩

theorem closed_sequence_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ receiver : ObservedReceiver fixture observed,
      Nonempty (SequenceWitness wordStages boolStages sequence receiver) := by
  obtain ⟨receiver⟩ := initial_receiver fixture observed
  exact ⟨receiver, sequence_meaning wordStages boolStages chooseWordStages chooseBoolStages sequence receiver⟩

end Tests.SourceCoreGenericDirect
end

section
-- leanmerge: from Solcore.Test.SourceCoreGenericDirectForward
/-! Following named execution derives sufficient public fuel from the independent
Source trace at the exact retained heap. The output and next history follow for
every sufficient resume of the original checkpoint. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

def ForwardAt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key arguments scalar.publicValue)
    (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome artifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion artifact,
        outcome = .succeeded completion ∧ completion.value = scalar.publicValue ∧
        completion.session.ExportsReady ∧
        ∃ returned : RetainedState support completion.session entries, returned.heap = after

theorem forward_call {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : RetainedState support session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    (scalar : ScalarOutput) (call : ObservedCall session key publicArguments scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers support.rows) fixture.recipePrepared
      call.checkpoint state.session key publicArguments runOptions.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall support request.header invocation state.heap arguments (.value scalar.source) after) :
    ForwardAt (entries := entries) support scalar call after := by
  obtain ⟨program, present⟩ := RecursiveNamedPublicHistoryRegistryExtension.diagnostics_present state.history
  have semantic : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics reason token →
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults state.receiving.result.diagnostics (.semantic reason) token := by
    intro reason token represented
    exact CompatibleRegistryDiagnosticExtension.semantic_preserved fixture.recipe.compiled
      receiver.issued state.issued present state.extension represented
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨receiving, contextAt, issued, extended, _diagnostics, _capture,
      payload, finalStore, finalMap, finalWorld, requiredExecution, requiredOutput,
      _nativeEnough, fullResult, publicEnough⟩ :=
    RecursiveNamedPublicActualRegistryNamedOutputPreservation.public_resume_has_sufficient_fuel
      (inputs := [support.wordInput, support.boolInput, support.chooseWordInput, support.chooseBoolInput]) (rows := support.rows)
      (stagePrepared := actualStagePrepared fixture) (completion := state.receiving)
      (receiver := state.issued) (profile := observed.profile) (observations := support.observations)
      (semantic := semantic) (family := support.family)
      (namedTerminals := support.terminals) (namedSupport := support.supports)
      (wellFormed := fixture.source_wellFormed) (prepared := fixture.recipePrepared)
      (selected := request.selected) (caller := state.caller) (history := state.history)
      (atCheckpoint := request.atCheckpoint) (started := request.started)
      (inputReceipts := inputs) (atRegistry := state.registry)
      (exportsReady := state.atSession.exportsReady_iff.mp ready) (sourceAt := sourceAt) applied
  have atRecipe : state.artifact.RecipeAt fixture.recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact) (recipe : SourceCoreIndexedSession.Recipe),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact _ atRecipe => by cases artifact; exact atRecipe
    exact convert _ _ state.atRecipe
  have requested := request.started.original.result_type_at atRecipe request.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result request.selected).2
  rw [resultType, rawType] at requested
  have nativeScalar : payload = scalar.native := by
    have represented := fullResult.2.1
    rw [nativeType] at represented
    cases represented with
    | value related => exact scalar.native_value related
  refine ⟨requiredExecution, requiredOutput, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, _generation, reached, succeeded, exported, actualAt,
      _related, history, registry, returnedReady⟩ :=
    publicEnough executionFuel outputFuel outcome executionBound outputBound resumed
  let returned : RetainedState support completion.session entries := {
    artifact := state.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := state.atRecipe
    receiving := receiving
    issued := issued
    extension := state.extension.trans extended
    registry := (congrArg (·.registry) contextAt).symm ▸ registry
    history := history }
  exact ⟨completion, succeeded, actualAt.1.trans (scalar.succeeded_value (nativeScalar ▸ exported) requested),
    actualAt.2.2.2.exportsReady_iff.mpr returnedReady, returned, rfl⟩

theorem CallMeaning.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {before : RetainedState support session []}
    {header : CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {scalar : ScalarOutput} {call : ObservedCall session key publicArguments scalar.publicValue}
    {arguments : List Dynamic.Value} {invocation : Staging.Recursive.Scope}
    (meaning : CallMeaning before header scalar call arguments invocation)
    (ready : session.ExportsReady) : ForwardAt (entries := []) support scalar call meaning.after.heap := by
  apply forward_call before scalar call meaning.request meaning.inputs meaning.rawType meaning.nativeType ready
  rw [meaning.headerEq]
  exact meaning.trace

structure ForwardMeaning {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : Prop where
  first : InitialForwardAt meaning.support sequence.first meaning.initial.heap
  second : ForwardAt (entries := []) meaning.support (.bool false) sequence.second meaning.secondMeaning.after.heap
  third : ForwardAt (entries := []) meaning.support (.word (Core.Word.ofNatModulo 33)) sequence.third meaning.thirdMeaning.after.heap
  fourth : ForwardAt (entries := []) meaning.support (.bool true) sequence.fourth meaning.fourthMeaning.after.heap

theorem SequenceWitness.forward {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {wordStages : ObservedStages fixture observed.wordRow.toObservedRow}
    {boolStages : ObservedStages fixture observed.boolRow.toObservedRow}
    {sequence : ObservedSequence fixture observed} {receiver : ObservedReceiver fixture observed}
    (meaning : SequenceWitness wordStages boolStages sequence receiver) : ForwardMeaning meaning := by
  have initialReady : sequence.first.session.ExportsReady :=
    (show sequence.first.bootstrap.ReadyAt 100000 sequence.first.session from .single sequence.first.ready).exportsReady
      sequence.first.authority
  have firstReady := sequence.first.executed.exportsReady initialReady
  have secondReady := sequence.second.executed.exportsReady firstReady
  have thirdReady := sequence.third.executed.exportsReady secondReady
  exact ⟨forward_initial meaning.support sequence.first meaning.firstTrace,
    meaning.secondMeaning.forward firstReady,
    meaning.thirdMeaning.forward secondReady,
    meaning.fourthMeaning.forward thirdReady⟩

theorem closed_forward_meaning (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (sequence : ObservedSequence fixture observed) :
    ∃ (receiver : ObservedReceiver fixture observed)
      (meaning : SequenceWitness wordStages boolStages sequence receiver), ForwardMeaning meaning := by
  obtain ⟨receiver, ⟨meaning⟩⟩ := closed_sequence_meaning fixture observed wordStages boolStages
    chooseWordStages chooseBoolStages sequence
  exact ⟨receiver, meaning, meaning.forward⟩

def runForward : IO Unit := do
  let fixture ← compiledFixture
  let observed ← observeProgram fixture
  let wordStages ← observeStages fixture observed.wordRow.toObservedRow
  let boolStages ← observeStages fixture observed.boolRow.toObservedRow
  let chooseWordStages ← observeStages fixture observed.chooseWordRow
  let chooseBoolStages ← observeStages fixture observed.chooseBoolRow
  let sequence ← observeSequence fixture observed
  have _meaning := closed_forward_meaning fixture observed wordStages boolStages chooseWordStages chooseBoolStages sequence
  IO.println "Generic direct calls: Word11, BoolFalse, Word33, BoolTrue; four Source histories and sufficient public fuel proved"

end Tests.SourceCoreGenericDirect
end
