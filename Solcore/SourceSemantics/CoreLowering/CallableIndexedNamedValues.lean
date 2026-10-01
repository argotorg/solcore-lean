import Solcore.SourceSemantics.CoreLowering.CallableNamedMetadata
import Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues
import Solcore.SourceSemantics.CoreLowering.NamedCallMeaning

/-! Named and builtin function leaves for the actual indexed artifact. Named
identity observes complete canonical declaration metadata and resolved evidence.
Static second-pass/installation equations and actual ambient-typed captures
certify the native carrier; no function-body execution follows from these laws.
Anonymous closures and source occurrence canonical-order provenance remain
separate obligations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Specialized := SourceSpecialization.SpecializedFunction
abbrev Evidence := SourceTypedRuntime.RuntimeEvidenceEnvironment

/-- Complete canonical plan and dictionary receipts. `target` ties source
metadata to the key through the real matcher, rather than replacing metadata
with that key. `slot` retains the actual singleton global selection. -/
structure Row {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (index : Nat) (signature : SourceCoreCalls.Signature) (specialized : Specialized) (evidence : Evidence) : Prop where
  slot : CallableNamedMetadata.Slot prepared.base.globals index signature
  record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized
  target : SourceCompilationPlan.exactInstantiationKey prepared.base.plan (CallableNamedMetadata.instantiation specialized) = .ok signature.key
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok evidence

/-- The ordinary compiler selection supplies the unique slot and complete
canonical record. The extra ordered-domain receipt records exactly what the
order-insensitive matcher did not check. -/
theorem Row.of_selected {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {metadata : DeclarationInstantiation}
    {isReference : Bool} {index : Nat} {signature : SourceCoreCalls.Signature}
    {specialized : Specialized} {evidence : Evidence}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (accepted : SourceCoreFunctions.selectedSignature policy compilation source node metadata isReference = .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    (domain : specialized.parameterSubstitution.map Prod.fst = metadata.parameterSubstitution.map Prod.fst)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok evidence) :
    Row prepared index signature specialized evidence ∧ metadata = CallableNamedMetadata.instantiation specialized := by
  have target := (NamedCalls.selected_signature_target accepted).1
  rw [plan] at target
  have same := (CallableNamedMetadata.matches_of_exact target record).canonical domain
  refine ⟨⟨?_, record, same ▸ target, resolved⟩, same⟩
  simpa only [globals] using CallableNamedMetadata.slot_of_selected_signature accepted

inductive Identity {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) : Dynamic.Value → Word → Prop where
  | builtin {source identity} (related : CallableIndexedBuiltinValues.Identity prepared source identity) : Identity prepared source identity
  | named {index signature specialized evidence identity}
      (row : Row prepared index signature specialized evidence)
      (number : Word.ofNat? (index + 1) = some identity) :
      Identity prepared (.global (CallableNamedMetadata.global specialized evidence)) identity

private theorem word_value {number : Nat} {word : Word} (accepted : Word.ofNat? number = some word) : word.val = number := by
  unfold Word.ofNat? at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

private theorem Row.source_eq_iff {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {i j : Nat} {a b : SourceCoreCalls.Signature} {f g : Specialized} {x y : Evidence}
    (left : Row prepared i a f x) (right : Row prepared j b g y) :
    i = j ↔ CallableNamedMetadata.global f x = CallableNamedMetadata.global g y := by
  constructor
  · intro same
    have signatures := Option.some.inj (left.slot.selected.symm.trans (same ▸ right.slot.selected))
    subst b
    have records := Except.ok.inj (left.record.symm.trans right.record)
    subst g
    have evidence := Except.ok.inj (left.resolved.symm.trans right.resolved)
    subst y
    rfl
  · intro same
    have headers := congrArg Dynamic.GlobalFunction.instantiation same
    change CallableNamedMetadata.instantiation f = CallableNamedMetadata.instantiation g at headers
    have selected := left.target
    rw [headers] at selected
    have keys := Except.ok.inj (selected.symm.trans right.target)
    exact (left.slot.unique right.slot keys).2

theorem identity_faithful {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked) :
    DataEquality.IdentityFaithful (Identity prepared) := by
  refine ⟨?_, ?_⟩
  · intro source identity related
    cases related with
    | builtin related => exact (CallableIndexedBuiltinValues.identity_faithful prepared).comparable related
    | named => exact .global _
  · intro first second a b left right
    cases left with
    | builtin left =>
      cases right with
      | builtin right => exact (CallableIndexedBuiltinValues.identity_faithful prepared).equal left right
      | named row number =>
        constructor
        · intro same
          exact False.elim (left.outside_globals (List.getElem?_eq_some_iff.mp row.slot.selected).choose number same)
        · intro same; cases left; cases same
    | named left numberA =>
      cases right with
      | builtin right =>
        constructor
        · intro same
          exact False.elim (right.outside_globals (List.getElem?_eq_some_iff.mp left.slot.selected).choose numberA same.symm)
        · intro same; cases right; cases same
      | named right numberB =>
        constructor
        · intro same
          have indices : _ := (word_value numberA).symm.trans ((congrArg Fin.val same).trans (word_value numberB))
          have equalIndices : _ := Nat.add_right_cancel indices
          exact congrArg Dynamic.Value.global (left.source_eq_iff right |>.mp equalIndices)
        · intro same
          have sources := Dynamic.Value.global.inj same
          have indices := (left.source_eq_iff right).mpr sources
          exact Option.some.inj (numberA.symm.trans (indices ▸ numberB))

/-- The code is the exact installed second-pass template at this global slot.
The capture environment and its typing are actual native data. This receipt
establishes static formation, not invocation meaning or arbitrary store history. -/
structure Native {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) (index : Nat) (signature : SourceCoreCalls.Signature)
    (body : Expr) (captured : Environment) : Prop where
  code : ∃ template, prepared.secondPass.closures[index]? = some template ∧
    SourceCoreCompatibleOutputs.installedTemplate index template =
      .lambda signature.parameterType (LanguageResult.resultType signature.resultType) body
  typed : RuntimeValueHasType world
    (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)
    signature.functionType prepared.layouts.definitions

inductive Represents {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | builtin {sourceType source value type}
      (related : CallableIndexedBuiltinValues.Represents prepared world sourceType source value type) :
      Represents prepared world sourceType source value type
  | named {index signature specialized evidence identity body captured}
      (row : Row prepared index signature specialized evidence)
      (number : Word.ofNat? (index + 1) = some identity)
      (projection : checked.catalog.project specialized.function.type = .ok
        (CallableContract.functionType signature.parameterType signature.resultType))
      (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
      (native : Native prepared world index signature body captured) :
      Represents prepared world specialized.function.type (.global (CallableNamedMetadata.global specialized evidence))
        (.pair (.pair (.inRight .unit (.word identity))
          (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)) (.word descriptor.id))
        (CallableContract.functionType signature.parameterType signature.resultType)

def model {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ _ world => Represents prepared world
  projection := by
    intro registry mapping _ _ _ _ _ related
    cases related with
    | builtin related => exact (CallableIndexedBuiltinValues.model prepared profile).projection (registry := registry) (mapping := mapping) related
    | named _ _ projection _ _ => exact projection
  runtime_hasType := by
    intro _ _ _ _ _ _ _ related
    cases related with
    | builtin related => exact related.runtime_hasType
    | named _ _ _ _ native => exact .pair (.pair (.inRight .word) native.typed) .word
  source_function := by
    intro _ _ _ _ _ _ _ related
    cases related with
    | builtin related => cases related; exact .builtin _
    | named => exact .global _
  extend := by
    intro _ _ _ _ _ _ _ _ _ _ related registries mappings worlds
    cases related with
    | builtin related => exact .builtin ((CallableIndexedBuiltinValues.model prepared profile).extend related registries mappings worlds)
    | named row number projection descriptor native =>
      exact .named row number projection descriptor ⟨native.code, native.typed.weaken worlds⟩

theorem observations {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) :
    FunctionObservations checked.catalog (model prepared profile) (Identity prepared) := by
  intro _ _ _ _ _ _ _ related
  cases related with
  | builtin related =>
    cases related with
    | builtin selected number descriptor _ => exact .contractedIdentified _ _ _ descriptor.id (.builtin (.builtin selected number)) profile
  | named row number _ descriptor _ => exact .contractedIdentified _ _ _ descriptor.id (.named row number) profile

theorem Represents.runtime_view {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : Represents prepared world sourceType source value type) : Dynamic.ValueRuntimeTypeMatches source sourceType := by
  cases related with
  | builtin related => cases related; exact (Dynamic.ValueRuntimeType.builtin _).matches
  | named => exact (Dynamic.ValueRuntimeType.global _).matches

theorem runtime_views {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) : FunctionRuntimeViews (model prepared profile) := by
  intro _ _ _ _ _ _ _ _ related
  exact related.runtime_view

/-- Actual native reference formation loads the exact installed closure and
wraps it without changing its captures or store. Source metadata and evidence
remain the complete canonical row. -/
theorem reference {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {index signature specialized evidence identity body captured world}
    (row : Row prepared index signature specialized evidence)
    (number : Word.ofNat? (index + 1) = some identity)
    (projection : checked.catalog.project specialized.function.type = .ok (CallableContract.functionType signature.parameterType signature.resultType))
    (descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
    (native : Native prepared world index signature body captured)
    {actual : Environment} {store : Store} {location : Location} {internalReason : Word}
    (selected : actual[index]? = some (.cellRef (OptionalCell.cellType signature.functionType) location))
    (read : store.read? location = some (.inRight .unit
      (.closure signature.parameterType (LanguageResult.resultType signature.resultType) body captured)))
    (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Evaluates actual store
      (LanguageResult.bind (CallableContract.functionType signature.parameterType signature.resultType)
        (SourceCoreFunctions.namedReference signature index identity internalReason)
        (LanguageResult.success (descriptor.wrap (.var 0)))) (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world specialized.function.type
        (.global (CallableNamedMetadata.global specialized evidence)) value
        (CallableContract.functionType signature.parameterType signature.resultType) :=
  ⟨_, NamedCalls.native_reference descriptor selected read, .named row number projection descriptor native⟩

/-- An ordinary accepted source reference supplies a fully represented global
value. Requirement-bearing references use `authenticated_evidence_eq` at their
separate evidence-policy branch; this theorem does not bypass that policy. -/
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
    (domain : specialized.parameterSubstitution.map Prod.fst = metadata.parameterSubstitution.map Prod.fst)
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
    (native : Native prepared world index signature body captured)
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
  have canonical := matched.canonical domain
  have resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok [] := by rw [assumptions]; rfl
  have row := (Row.of_selected prepared plan globals selection record domain resolved).1
  have sourceTrace := NamedCalls.accepted_named_reference (program := program) (evidence := evidence)
    (sourceEnvironment := sourceEnvironment) (heap := heap) prepared.ancestry.graph.inputs.callable active
    owner found readNode form special accepted selection number callables descriptor descriptorAccepted
    coercions requirements valid (by rw [noPredicates]; exact .nil) globalReference globalPayload
  refine ⟨_, sourceTrace.2.2.1, sourceTrace.2.2.2.1, ?_, sourceTrace.2.2.2.2⟩
  rw [canonical]
  exact .named row number projection descriptor native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedValues
