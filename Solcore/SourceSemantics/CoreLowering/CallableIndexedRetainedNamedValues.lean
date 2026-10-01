import Solcore.SourceSemantics.CoreLowering.CallableNamedCanonicalOrder
import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedValues

/-! The actual checker's retained named metadata uses the opposite parameter
ledger order from the specialization record. This separate leaf model
transports complete source values by an explicit involution. Canonical and
retained source values are never identified inside one identity relation.
Evidence, raw type, native code and actual captures are unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedRetainedNamedValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev Evidence := SourceTypedRuntime.RuntimeEvidenceEnvironment

inductive Identity {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) : Dynamic.Value → Word → Prop where
  | retained {source identity} (canonical : CallableIndexedNamedValues.Identity prepared source identity) :
      Identity prepared (CallableNamedReversal.value source) identity

theorem identity_faithful {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    DataEquality.IdentityFaithful (Identity prepared) := by
  refine ⟨?_, ?_⟩
  · intro source identity related
    cases related with
    | retained canonical =>
      cases canonical with
      | builtin related => cases related; exact .builtin _
      | named => exact .global _
  · intro first second a b left right
    cases left with
    | retained left =>
      cases right with
      | retained right =>
        constructor
        · intro same
          exact congrArg CallableNamedReversal.value ((CallableIndexedNamedValues.identity_faithful prepared).equal left right |>.mp same)
        · intro same
          exact (CallableIndexedNamedValues.identity_faithful prepared).equal left right |>.mpr (CallableNamedReversal.value_injective same)

inductive Represents {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | retained {sourceType source value type}
      (canonical : CallableIndexedNamedValues.Represents prepared world sourceType source value type) :
      Represents prepared world sourceType (CallableNamedReversal.value source) value type

def model {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ _ world => Represents prepared world
  projection := by
    intro registry mapping _ _ _ _ _ related
    cases related with
    | retained canonical => exact (CallableIndexedNamedValues.model prepared profile).projection (registry := registry) (mapping := mapping) canonical
  runtime_hasType := by
    intro registry mapping _ _ _ _ _ related
    cases related with
    | retained canonical => exact (CallableIndexedNamedValues.model prepared profile).runtime_hasType (registry := registry) (mapping := mapping) canonical
  source_function := by
    intro _ _ _ _ _ _ _ related
    cases related with
    | retained canonical =>
      cases canonical with
      | builtin related => cases related; exact .builtin _
      | named => exact .global _
  extend := by
    intro _ _ _ _ _ _ _ _ _ _ related registries maps worlds
    cases related with
    | retained canonical => exact .retained ((CallableIndexedNamedValues.model prepared profile).extend canonical registries maps worlds)

theorem observations {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionObservations checked.catalog (model prepared profile) (Identity prepared) := by
  intro _ _ _ _ _ _ _ related
  cases related with
  | retained canonical =>
    cases canonical with
    | builtin related =>
      cases related with
      | builtin selected number descriptor _ =>
        exact .contractedIdentified _ _ _ descriptor.id (.retained (.builtin (.builtin selected number))) profile
    | named row number _ descriptor _ => exact .contractedIdentified _ _ _ descriptor.id (.retained (.named row number)) profile

theorem Represents.runtime_view {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : Represents prepared world sourceType source value type) : Dynamic.ValueRuntimeTypeMatches source sourceType := by
  cases related with
  | retained canonical =>
    cases canonical with
    | builtin related => cases related; exact (Dynamic.ValueRuntimeType.builtin _).matches
    | named => exact (Dynamic.ValueRuntimeType.global _).matches

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) : FunctionRuntimeViews (model prepared profile) := by
  intro _ _ _ _ _ _ _ _ related
  exact related.runtime_view

/-- The actual matcher accepts either ledger order. Thus a selected retained
occurrence supplies the old canonical target receipt without an extra lookup
assumption. All remaining fields are retained in `same`. -/
theorem row_of_selected {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {metadata : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : Specialized} {evidence : Evidence}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node metadata isReference = .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    (same : metadata = CallableNamedReversal.instantiation (CallableNamedMetadata.instantiation specialized))
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok evidence) :
    CallableIndexedNamedValues.Row prepared index signature specialized evidence := by
  have target := (NamedCalls.selected_signature_target accepted).1
  rw [plan, same, CallableNamedReversal.target_reverse] at target
  exact ⟨by simpa only [globals] using CallableNamedMetadata.slot_of_selected_signature accepted, record, target, resolved⟩

/-- Actual declaration construction and successful specialization supply the
reverse-order source header. No equality of whole source records is assumed. -/
theorem row_of_inferred {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {metadata : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : Specialized} {evidence : Evidence}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node metadata isReference = .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    {sourceSignature : ProgramFunctionSignature} {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    (specialization : SourceSpecialization.specializeFunction sourceSignature function supplied = .ok specialized)
    (unique : sourceSignature.scheme.parameters.Nodup)
    (next : Nat) (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (formed : metadata = CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok evidence) :
    CallableIndexedNamedValues.Row prepared index signature specialized evidence ∧
      metadata = CallableNamedCanonicalOrder.retainedInstantiation specialized := by
  have target := (NamedCalls.selected_signature_target accepted).1
  rw [plan] at target
  have matched := CallableNamedMetadata.matches_of_exact target record
  rw [formed] at matched
  have same := formed.trans (matched.retained_of_specialization specialization unique next final caller)
  exact ⟨row_of_selected prepared plan globals accepted record same resolved, same⟩

/-- Actual target selection and evidence authentication identify every field
of a retained source global. This also covers nonempty dictionaries at the
metadata boundary; extracting their materialization from the qualified
lowering branch remains a separate obligation. -/
theorem global_of_inferred {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {key : SourceCompilationPlan.Key} {metadata : DeclarationInstantiation} {specialized : Specialized}
    {sourceSignature : ProgramFunctionSignature} {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    (specialization : SourceSpecialization.specializeFunction sourceSignature function supplied = .ok specialized)
    (unique : sourceSignature.scheme.parameters.Nodup)
    (next : Nat) (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (formed : metadata = CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller)
    (selected : SourceCompilationPlan.exactInstantiationKey plan metadata = .ok key)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok specialized)
    {actual canonical : Evidence} {semantic : Dynamic.EvidenceEnvironment}
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key specialized.assumptions actual = .ok ())
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key specialized.assumptions = .ok canonical)
    (represented : Forall₂ (fun item entry => entry.1 = SourceTypedRuntime.runtimeEvidenceGoal item ∧
      ImplementationEvidenceRepresents item entry.2) actual semantic) :
    (⟨metadata, semantic⟩ : Dynamic.GlobalFunction) =
      CallableNamedReversal.global (CallableNamedMetadata.global specialized canonical) := by
  have matched := CallableNamedMetadata.matches_of_exact selected record
  rw [formed] at matched
  have same := formed.trans (matched.retained_of_specialization specialization unique next final caller)
  rw [same, CallableNamedMetadata.environment_eq_of_represents represented,
    CallableNamedMetadata.authenticated_evidence_eq authenticated resolved]
  rfl

/-- The complete accepted ordinary reference forms the retained source value,
including its parameter order. The real instantiation/specialization receipts
discharge full metadata equality through the order bridge. Qualified evidence
policy extraction is a separate branch. -/
theorem formation_of_accepted {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {name : String} {metadata : DeclarationInstantiation} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {index : Nat} {signature : SourceCoreCalls.Signature} {identity : Word} {specialized : Specialized}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (owner : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (readNode : policy.readExpression source id = .ok (node, type))
    (form : node.form = .reference name (.declaration metadata))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered)
    (selection : SourceCoreFunctions.selectedSignature policy compilation source node metadata true = .ok (index, signature))
    (number : Word.ofNat? (index + 1) = some identity)
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    {sourceSignature : ProgramFunctionSignature} {function : CheckedFunction} {supplied : TypeSystem.ParameterSubstitution}
    (specialization : SourceSpecialization.specializeFunction sourceSignature function supplied = .ok specialized)
    (unique : sourceSignature.scheme.parameters.Nodup)
    (next : Nat) (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (formed : metadata = CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller)
    (projection : checked.catalog.project specialized.function.type = .ok (CallableContract.functionType signature.parameterType signature.resultType))
    (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
    (descriptorAccepted : SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key) = .ok descriptor)
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {sourceEnvironment : Dynamic.Environment} {heap : Dynamic.Heap}
    (coercions : node.coercions = []) (requirements : Dynamic.OrdinaryRequirementLayout node.requirements node.coercions [])
    (valid : SourceSemantics.DeclarationInstantiation.Valid context metadata)
    {world : StoreTyping} {actual captured : Environment} {store : Store} {location : Location} {body : Expr}
    (native : CallableIndexedNamedValues.Native prepared world index signature body captured)
    (globalReference : actual[scope.length + compilation.administrativePrefix + index]? =
      some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (globalPayload : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Dynamic.ExpressionEvaluates program context evidence source sourceEnvironment heap id (.global ⟨metadata, []⟩) heap ∧
      Evaluates actual store lowered.expression (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world metadata.type (.global ⟨metadata, []⟩) value
        (CallableContract.functionType signature.parameterType signature.resultType) ∧
      (∀ result finalStore, Evaluates actual store lowered.expression result finalStore → result = .inRight .word value ∧ finalStore = store) := by
  obtain ⟨chosen, selectedRecord, matched, assumptions, _⟩ := CallableNamedMetadata.metadata_of_selected_signature selection
  rw [plan] at selectedRecord
  have same := Except.ok.inj (selectedRecord.symm.trans record)
  subst chosen
  have noPredicates : metadata.predicates = [] := matched.predicates.symm.trans assumptions
  have resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok [] := by rw [assumptions]; rfl
  obtain ⟨row, sameMetadata⟩ := row_of_inferred prepared plan globals selection record specialization unique next final caller formed resolved
  have sourceTrace := NamedCalls.accepted_named_reference (program := program) (evidence := evidence)
    (sourceEnvironment := sourceEnvironment) (heap := heap) prepared.ancestry.graph.inputs.callable active
    owner found readNode form special accepted selection number callables descriptor descriptorAccepted
    coercions requirements valid (by rw [noPredicates]; exact .nil) globalReference globalPayload
  refine ⟨_, sourceTrace.2.2.1, sourceTrace.2.2.2.1, ?_, sourceTrace.2.2.2.2⟩
  rw [sameMetadata]
  exact .retained (.named row number projection descriptor native)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedRetainedNamedValues
