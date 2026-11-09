import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionRecursive
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ChosenOrdinaryCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSourceSelection
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.NamedHeaderReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalNamedCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.BranchingTrees
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.IndirectCalls
import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins

/-!
# Staged bounds: named bodies

Prepared named bodies: receipts and ports, read diagnostics, invocation, application and parent bounds, and method path typing.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
/-! The actual prepared named compiler and its receiving diagnostic table
supply fault interpretation only for certified local reads. The same read
certificate selects the original binder, occurrence and span. No blanket
interpretation for unrelated expressions or Source execution is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedOwnedPublicFaultReceiverTables

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)

include diagnostic aligned receiver in
/-- The complete issuer and exact receiver construct the diagnostic for this
accepted read. Its lexical Source binder and span come from the certificate. -/
theorem decoded_read {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reason : Word} {code : Expr}
    (certificate : CompatibleExpressionReads.Certificate fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      header.function.source scope id reason code)
    (token : reason = header.reasonAt id) :
    completion.result.diagnostics.diagnostic? reason = some {
      error := .uninitializedLocal certificate.binder
      site := .occurrence id.occurrence
      span := some certificate.node.span } := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have source : header.function.source = prepared.named.specialized.function.typedBody := by
    rw [aligned.function]
    rfl
  have unique : NodeOccurrencesUnique prepared.named.specialized.function.typedBody :=
    source ▸ header.unique
  have contains : ContainsExpression prepared.named.specialized.function.typedBody id certificate.node :=
    source ▸ lookupExpression?_sound certificate.metadata.found
  have sameBase : prepared.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  have ownFound := prepared.compilation.diagnostic
  rw [sameBase] at ownFound
  have reasonEq : header.reasonAt id = issued.program.reasonAt prepared.named.signature.key id := by
    rw [aligned.reasonAt, lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  obtain ⟨read, _expression, _binder, _span, readToken, _member, decoded⟩ :=
    CompatiblePublicContextualDiagnosticObservations.receiver_local_read_diagnostic
      compiled receiver present
      (CallableIndexedActualNamedSourceReceipts.cached_record compiled prepared.selected prepared.compilation.hook)
      unique contains certificate.form ownFound
  simpa only [← readToken, ← reasonEq, ← token] using decoded

include diagnostic aligned receiver in
/-- A certified read receives the concrete semantic fault interpretation.
The original Source fault retains its location in its independent trace. -/
theorem uninitialized {fuel : Nat} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      header.function.source context header.reasonAt scope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics
      (.uninitializedLocation location) (header.reasonAt id) := by
  obtain ⟨certificate, _type, _binding⟩ := receipt
  apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
  exact CallableIndexedOwnedPublicDecodedAssignmentFaults.of_decoded
    (decoded_read prepared diagnostic aligned receiver certificate rfl)
    (.readUninitialized location certificate.binder)

include diagnostic aligned receiver in
/-- The same concrete diagnostic keeps the semantic tag in recursive staging. -/
theorem staged_uninitialized {fuel : Nat} {context : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionReads.LoweredRead fuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      header.function.source context header.reasonAt scope id lowered)
    (location : Dynamic.Location) :
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics
      (.semantic (.uninitializedLocation location)) (header.reasonAt id) :=
  CallableIndexedOwnedPublicDecodedStagedCallFaults.of_semantic
    (uninitialized prepared diagnostic aligned receiver receipt location)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedReadDiagnostics
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionGoal
/-! Original operator typing and the actual materialized primary requirement
identify an admissible selection goal before any method body is instantiated. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionGoal
open Core Frontend SourceInference
open CallablePreparedMethodRuntimeMeaning
open CallablePreparedOperatorSourceBounds
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)

variable {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy lowerBody fuel compilation values source scope id reasonAt lowered)
  (selected : OperatorSource receipt.operator)
  {context : SourceSemantics.Context}

include selected in
private theorem primary_admissible
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id receipt.node.type) :
    ∃ goal, PredicateAdmissible context goal ∧
      RequirementProves context receipt.operator.selection.primaryRequirement goal := by
  generalize _typeEq : receipt.node.type = annotation at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw rawEq _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.operator.found)
    subst actualNode
    have layout := CallableCallRequirementLayouts.ordinary_owned receipt.operator.ordinary
    rcases receipt.operator.form with ⟨operator, operandId, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
    · rw [form] at raw
      cases raw with
      | unary child operatorTyped =>
        cases valid with
        | ordinary _ path requirements =>
          have ownedEq := List.append_cancel_right (layout.symm.trans requirements)
          rw [receipt.metadata.coercions] at path
          generalize targetEq : receipt.node.type = target at path
          cases path
          cases operatorTyped with
          | logicalNot | wordBitNot | integerBitNot => exact False.elim (receipt.operator.nonempty ownedEq)
          | trait dispatch profile proves =>
            cases profile with
            | @intro signature method parameter member name parameters methodUnique inputs results =>
              refine ⟨{ trait := .declaration signature.id, subject := _, arguments := [] }, ⟨child.type_admissible, by simp, signature, member, rfl, ?_⟩, ?_⟩
              · simp [parameters]
              · exact RequirementSequenceProves.head (selected.requirements ▸ ownedEq.symm ▸ proves)
    · rw [form] at raw
      cases raw with
      | binary first second operatorTyped =>
        cases valid with
        | ordinary _ path requirements =>
          have ownedEq := List.append_cancel_right (layout.symm.trans requirements)
          rw [receipt.metadata.coercions] at path
          generalize targetEq : receipt.node.type = target at path
          cases path
          cases operatorTyped with
          | wordArithmetic _ | integerArithmetic _ | wordShift _ | wordUnchecked _ | wordComparison _ | integerComparison _ | booleanAnd | booleanOr =>
            exact False.elim (receipt.operator.nonempty ownedEq)
          | trait dispatch profile proves =>
            cases profile with
            | @intro signature method parameter member name parameters methodUnique inputs results =>
              refine ⟨{ trait := .declaration signature.id, subject := _, arguments := [] }, ⟨first.type_admissible, by simp, signature, member, rfl, ?_⟩, ?_⟩
              · simp [parameters]
              · exact RequirementSequenceProves.head (selected.requirements ▸ ownedEq.symm ▸ proves)

/-- The real primary evidence and the typed operator share one stable ledger
identity, so the selected head goal inherits complete raw type admission. -/
theorem admissible
    (signatures : context.signatures = receipt.program.signatures)
    (ledger : context.solvedRequirements = receipt.caller.function.solvedRequirements)
    (assumptions : ∀ goal, goal ∈ receipt.caller.assumptions → goal ∈ context.assumptions)
    (unique : NodeOccurrencesUnique source)
    (idsUnique : RequirementIdsUnique context)
    (typed : ExpressionHasType source context id receipt.node.type) :
    PredicateAdmissible context selected.certificate.selected.goal := by
  obtain ⟨goal, admitted, proves⟩ := primary_admissible receipt selected unique typed
  have produced := CallableCoercionSourceSelection.requirement_produces signatures ledger assumptions
    receipt.operator.resolved selected.certificate.roots.primarySelected selected.certificate.roots.primaryValid
  have primaryGoal : SourceCompilationPlan.runtimeEvidenceGoal selected.certificate.roots.primary =
      selected.certificate.selected.goal :=
    congrArg SourceCompilationPlan.runtimeEvidenceGoal selected.certificate.selected.primaryShape
  have same := idsUnique.proves_predicate_eq proves produced.requirement_valid
  exact same.trans primaryGoal ▸ admitted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionGoal
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionRanges
/-! Actual implementation-head matching recovers every ordered replacement
from an admitted goal. Concrete specialization then closes its raw catalog type. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionRanges
open Frontend TypeSystem

private def applicationArguments : Ty → List Ty
  | .application head argument => applicationArguments head ++ [argument]
  | _ => []

private theorem arguments_applyMany (head : Ty) (arguments : List Ty) :
    applicationArguments (Ty.applyMany head arguments) = applicationArguments head ++ arguments := by
  induction arguments generalizing head with
  | nil => simp [Ty.applyMany]
  | cons argument rest ih =>
    change applicationArguments (Ty.applyMany (.application head argument) rest) = _
    rw [ih]
    simp [applicationArguments, List.append_assoc]

private theorem arguments_nominal (declaration : Resolved.DeclarationId) (arguments : List Ty) :
    applicationArguments (Ty.nominal declaration arguments) = arguments := by
  simp [Ty.nominal, arguments_applyMany, applicationArguments]

private theorem scoped_arguments {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ argument ∈ applicationArguments type, TypeWellScoped context variables argument := by
  cases typed with
  | nominal declaration arguments member arity typed
  | contractNominal declaration arguments member arity typed =>
    rw [arguments_nominal]
    intro argument member
    exact typed.member member
  | _ => simp [applicationArguments]

private def applicationHead : Ty → Ty
  | .application head _ => applicationHead head
  | other => other

private theorem head_applyMany (head : Ty) (arguments : List Ty) :
    applicationHead (Ty.applyMany head arguments) = applicationHead head := by
  induction arguments generalizing head with
  | nil => rfl
  | cons argument rest ih => exact ih (.application head argument)

private theorem nominal_ne_proxy (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .proxy inner := by
  intro same
  have heads := congrArg applicationHead same
  simp [Ty.nominal, head_applyMany, applicationHead] at heads

private theorem nominal_ne_comptime (declaration : Resolved.DeclarationId) (arguments : List Ty) (inner : Ty) :
    Ty.nominal declaration arguments ≠ .comptime inner := by
  intro same
  have heads := congrArg applicationHead same
  simp [Ty.nominal, head_applyMany, applicationHead] at heads

private theorem scoped_proxy {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ inner, type = .proxy inner → TypeWellScoped context variables inner := by
  cases typed with
  | nominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_proxy declaration.id arguments inner same)
  | contractNominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_proxy declaration.id arguments inner same)
  | proxy inner => intro _ same; cases same; exact inner
  | _ => intro _ same; cases same

private theorem scoped_comptime {context : Context} {variables : List TypeVarId} {type : Ty}
    (typed : TypeWellScoped context variables type) :
    ∀ inner, type = .comptime inner → TypeWellScoped context variables inner := by
  cases typed with
  | nominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_comptime declaration.id arguments inner same)
  | contractNominal declaration arguments _ _ _ => exact fun inner same => False.elim (nominal_ne_comptime declaration.id arguments inner same)
  | comptime inner => intro _ same; cases same; exact inner
  | _ => intro _ same; cases same

private theorem occurs_applyMany (parameter : TypeParameterId) (head : Ty) (arguments : List Ty) :
    TypeParameterOccurs parameter (Ty.applyMany head arguments) ↔
      TypeParameterOccurs parameter head ∨ ∃ argument ∈ arguments, TypeParameterOccurs parameter argument := by
  induction arguments generalizing head with
  | nil => simp [Ty.applyMany]
  | cons argument rest ih =>
    change TypeParameterOccurs parameter (Ty.applyMany (.application head argument) rest) ↔ _
    rw [ih]
    simp only [TypeSystem.TypeParameterOccurs, List.mem_cons, exists_eq_or_imp, or_assoc]

private theorem occurs_nominal {parameter : TypeParameterId} {declaration : Resolved.DeclarationId} {arguments : List Ty}
    (occurs : TypeParameterOccurs parameter (Ty.nominal declaration arguments)) :
    ∃ argument ∈ arguments, TypeParameterOccurs parameter argument := by
  rcases (occurs_applyMany parameter (.constructor (.declaration declaration)) arguments).mp occurs with impossible | found
  · cases impossible
  · exact found

/-- The original well-scoped head prevents parameters from appearing in an
ill-formed nominal head with missing arguments. Each genuine occurrence recovers its replacement. -/
private theorem scoped_at_occurrence {original target : Context} {originalVariables variables : List TypeVarId}
    (substitution : TypeSystem.ParameterSubstitution) {type : Ty}
    (originalTyped : TypeWellScoped original originalVariables type) :
    ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)) := by
  refine TypeWellScoped.rec
    (motive_1 := fun type _ => ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)))
    (motive_2 := fun types _ => ∀ type ∈ types, ∀ parameter, TypeParameterOccurs parameter type →
      TypeWellScoped target variables (substitution.apply type) →
      TypeWellScoped target variables ((substitution.lookup? parameter).getD (.parameter parameter)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ originalTyped
  · intro metavariable bound parameter occurs; cases occurs
  · intro actual bound owned parameter occurs typed
    cases occurs
    exact typed
  · intro builtin parameter occurs; cases occurs
  · intro declaration arguments cataloged arity originalTyped ih parameter occurs typed
    obtain ⟨argument, member, occurs⟩ := occurs_nominal occurs
    apply ih argument member parameter occurs
    rw [StructuralSubstitution.apply_nominal] at typed
    exact scoped_arguments typed _ (by rw [arguments_nominal]; exact List.mem_map.mpr ⟨argument, member, rfl⟩)
  · intro declaration arguments cataloged arity originalTyped ih parameter occurs typed
    obtain ⟨argument, member, occurs⟩ := occurs_nominal occurs
    apply ih argument member parameter occurs
    rw [StructuralSubstitution.apply_nominal] at typed
    exact scoped_arguments typed _ (by rw [arguments_nominal]; exact List.mem_map.mpr ⟨argument, member, rfl⟩)
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.function_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.function_components _ _ rfl).2
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.product_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.product_components _ _ rfl).2
  · intro left right first second leftIH rightIH parameter occurs typed
    rcases occurs with occurs | occurs
    · exact leftIH parameter occurs (typed.mapping_components _ _ rfl).1
    · exact rightIH parameter occurs (typed.mapping_components _ _ rfl).2
  · intro inner originalTyped ih parameter occurs typed
    exact ih parameter occurs (scoped_proxy typed _ rfl)
  · intro inner originalTyped ih parameter occurs typed
    exact ih parameter occurs (scoped_comptime typed _ rfl)
  · intro type member; cases member
  · intro head tail headTyped tailTyped headIH tailIH type member
    rcases List.mem_cons.mp member with rfl | member
    · exact headIH
    · exact tailIH type member

private theorem admissible_at_occurrence
    {original context : Context} {originalVariables : List TypeVarId}
    (substitution : TypeSystem.ParameterSubstitution) {type : Ty} {parameter : TypeParameterId}
    (originalTyped : TypeWellScoped original originalVariables type)
    (occurs : TypeParameterOccurs parameter type)
    (admitted : TypeAdmissible context (substitution.apply type)) :
    TypeAdmissible context ((substitution.lookup? parameter).getD (.parameter parameter)) := by
  have replacementScoped := scoped_at_occurrence substitution originalTyped parameter occurs admitted.typeWellScoped
  cases residual : context.residualTypeVariables with
  | false =>
    exact ⟨admitted.binders, by simpa [admissibleTypeVariables, residual] using replacementScoped⟩
  | true =>
    exact StructuralSubstitution.TypeWellScoped.toAdmissibleOfResidual admitted.binders residual replacementScoped

/-- Every original implementation parameter occurs in its well-formed head.
The genuine selected head equation identifies the admitted replacement, and
actual specialization acceptance supplies its full concrete check. -/
theorem of_selected
    {program : CheckedProgram} {primary : TypedTraitResolution.Evidence}
    {name : String} {method : ExecutableImplMethods.CheckedMethod}
    (selected : CallableCoercionMethodInstantiation.Selection program primary name method)
    (wellFormed : ProgramWellFormed (Program.ofChecked program))
    (formed : CallableCoercionMethodInstantiation.Formation selected.implementation selected.declaration)
    {context : Context} (signatures : context.signatures = program.signatures)
    (admitted : PredicateAdmissible context selected.goal) :
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures program.signatures) method.specialized.parameterSubstitution := by
  let substitution := method.specialized.parameterSubstitution
  have original := wellFormed.signatures.implementations_semantic selected.implementation selected.implementationMember
  have determined := selected.determines formed
  have headEq := determined.2.2
  rw [← headEq] at admitted
  intro parameter replacement member
  have parameterMember : parameter ∈ selected.implementation.parameters := by
    rw [← selected.domain]
    exact List.mem_map.mpr ⟨(parameter, replacement), member, rfl⟩
  have lookup := StructuralSubstitution.ParameterSubstitution.lookup?_eq_some_of_mem_of_domain_nodup
    (selected.exact_substitution formed.parameters).domain_nodup member
  have replacementAdmitted : TypeAdmissible context replacement := by
    rcases original.parameters_in_head parameter parameterMember with occurs | ⟨argument, argumentMember, occurs⟩
    · have recovered := admissible_at_occurrence substitution original.head.subject.typeWellScoped occurs admitted.subject
      simpa only [substitution, lookup, Option.getD_some] using recovered
    · have argumentAdmitted : TypeAdmissible context (substitution.apply argument) :=
        admitted.arguments _ (List.mem_map.mpr ⟨argument, argumentMember, rfl⟩)
      have recovered := admissible_at_occurrence substitution
        (original.head.arguments argument argumentMember).typeWellScoped occurs argumentAdmitted
      simpa only [substitution, lookup, Option.getD_some] using recovered
  have concrete := SourceSpecializationAcceptance.specializeFunction_parameterReplacement_concrete
    selected.specialized parameter replacement lookup
  have closed := CallableIndexedOwnedReachedNamedConcreteRangeReceipts.admissible_concrete_at_catalog
    replacementAdmitted concrete
  simpa only [signatures] using closed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSelectionRanges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
/-! Internal body ports separate authentic named parameter entry and caller
restoration from statement shape. Reflection keeps the actual final Source
context, including locals introduced while evaluating the body. Static compiler
packets and strict child induction supply these ports. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header OwnedKey)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedNamedChildBounds (poolBridge)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (child : Staging.Recursive.Scope)
  (faults : RecursiveStageMeaning.FaultRep) (budget : Nat)

/-- Full Source-to-native body meaning at the real reached parameter state. -/
def PreservesBelow : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (_environments : DataHeap.EnvRepresents catalog mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions)
    (_heaps : GenericHeap.HeapRepresents model mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : State headers keys
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
    (_admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context initial)
    (owner : OwnedKey keys)
    (_packet : owner.key.capturePrefix = 0 → header.globals = compiled.indexed.base.globals.length →
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial),
    ∀ {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (_trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size child
      header.context environment before header.function.body finalContext bodyOutcome after)
    (_matched : Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome)
    (_within : size ≤ budget),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (header.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached

/-- Native-to-Source body meaning with its actual final lexical context. -/
def ReflectsBelow : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (_environments : DataHeap.EnvRepresents catalog mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions)
    (_heaps : GenericHeap.HeapRepresents model mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : State headers keys
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
    (_admitted : Admission (poolBridge (headers := headers) (keys := keys)) header.context initial)
    (owner : OwnedKey keys)
    (_packet : owner.key.capturePrefix = 0 → header.globals = compiled.indexed.base.globals.length →
    CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial),
    ∀ {size : Nat} {value : Value} {finalStore : Store}
    (_completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore)
    (_within : size ≤ budget),
    ∃ sourceSize finalContext bodyOutcome outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize child
        header.context environment before header.function.body finalContext bodyOutcome after ∧
      Staging.Recursive.BodyResult header.function.resultType
        bodyOutcome outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : State headers keys
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (poolBridge (headers := headers) (keys := keys)) header.context header.function.resultType outcome reached

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodyPorts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReceipts
/-! The lexical alternative retains the accepted statement action and exact
body footer of one authentic named Header. This receipt has no semantic
children, Source trace, execution law or completed result. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CompatibleEncoding (bind_ok)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def parameterScope (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : SourceCoreLocalCell.Scope :=
  header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))

structure Receipt (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  flow : Expr
  accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy header.policy header.fuel header.function.source
    (parameterScope header) header.function.body header.output header.reasonAt true header.escaped = .ok flow
  emitted : header.body = CompatibleStatements.finish header.output flow header.fellThrough header.escaped
  shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape header.function.source header.function.body
  projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output

/-- Inversion uses the one accepted Header body action, preserving its actual
flow code and diagnostic words. -/
theorem of_accepted {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy header.policy header.fuel header.function.source
      (parameterScope header) header.function.body header.output header.reasonAt header.fellThrough header.escaped =
        .ok header.body)
    (shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape header.function.source header.function.body)
    (projection : compiled.compatible.checked.catalog.project header.function.resultType = .ok header.output) :
    Nonempty (Receipt header) := by
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  exact ⟨⟨flow, generated, (Except.ok.inj returned).symm, shape, projection⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedLexicalReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodPathTyping
/-! Recover original method-parent typing along an authentic certificate path. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodPathTyping
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate MethodCalls)

private theorem typed_at_lookup {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) :
    ExpressionHasType source context id node.type := by
  obtain ⟨actual, contains, stored⟩ := typed.stored_type
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  subst actual
  exact stored ▸ typed

private theorem row_member {source : TypedSource} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    (typed : ExpressionsHaveTypes source context ids types)
    {id : ExpressionId} (member : id ∈ ids) :
    ∃ type, ExpressionHasType source context id type := by
  induction ids generalizing types with
  | nil => cases member
  | cons head tail ih =>
    cases typed with
    | cons headTyped tailTyped =>
      rcases List.mem_cons.mp member with same | remaining
      · subst id; exact ⟨_, headTyped⟩
      · exact ih tailTyped remaining

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
  {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
  {callId : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndexedOwnedPreparedStagedOperatorMethodCertificates.Receipt
    policy body callFuel compilation values source callScope callId reasonAt lowered)

theorem parent_typed
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context rootId type)
    (path : MethodCalls compiler root) :
    ExpressionHasType source context callId compiler.node.type := by
  induction path generalizing type with
  | here sequence children =>
    exact typed_at_lookup unique compiler.metadata.found typed
  | @method_child scope id otherFuel code types outer sequence children child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique outer.metadata.found typed
    obtain ⟨rawTypes, childrenTyped⟩ := outer.arguments_typed unique originalTyped
    obtain ⟨childType, childTyped⟩ := row_member childrenTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @group scope id node inner innerNode code actual form found sourceType child inside ih =>
    have originalTyped := typed_at_lookup unique actual.found typed
    obtain ⟨actualInner, childFound, sameType, childTyped⟩ :=
      CompatibleExpressionProducts.group_source_types
        unique actual.found form actual.coercions originalTyped
    exact ih childTyped
  | @tuple_child scope id node tupleIds types codes header sequence children
      child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique header.metadata.found typed
    obtain ⟨rawTypes, childrenTyped, sameType⟩ :=
      CompatibleExpressionTuples.source_types unique header.metadata.found
        header.form header.metadata.coercions originalTyped
    obtain ⟨childType, childTyped⟩ :=
      row_member childrenTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @constructor_child scope id node instantiation constructorIds tag headerWord codes header form admissible ranges count nodes sequence children child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique header.metadata.found typed
    obtain ⟨_admissible, childrenTyped, _sameType⟩ :=
      CompatibleExpressionConstructors.constructor_source_types unique header.metadata.found
        form header.metadata.coercions originalTyped
    obtain ⟨childType, childTyped⟩ := row_member childrenTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @builtin_child scope id otherCallee otherIds function otherFuel code
      outer calleeTyped sourceType nativeTypes sequence children child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique outer.metadata.found typed
    obtain ⟨_callee, argumentsTyped, _sourceType⟩ :=
      CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.source_types
        unique outer.metadata.found outer.form outer.metadata.coercions originalTyped
    obtain ⟨childType, childTyped⟩ := row_member argumentsTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @direct_child scope id otherCallee otherIds otherInstantiation otherFuel code types
      outer calleeTyped application sequence children child childCode member inside ih =>
    have originalTyped := typed_at_lookup unique outer.metadata.found typed
    obtain ⟨rawTypes, _callee, _application, argumentsTyped⟩ :=
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types
        unique outer.metadata.found outer.form outer.metadata.coercions originalTyped
    obtain ⟨childType, childTyped⟩ := row_member argumentsTyped (List.of_mem_zip member).1
    exact ih childTyped
  | @call_child scope id otherCallee otherIds otherMetadata otherFuel code types
      outer sequence children child childCode member inside ih =>
    obtain ⟨parameter, result, rawTypes, calleeTyped, argumentsTyped, application⟩ :=
      CallableIndexedOwnedStoredClosureArgumentReceipts.original_facts
        unique outer.found outer.originalForm typed
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      exact ih calleeTyped
    · obtain ⟨childType, childTyped⟩ :=
        row_member argumentsTyped (List.of_mem_zip remaining).1
      exact ih childTyped

  | @unary_child scope id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType profile child inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualChild, actualCore, childFound, childTyped, actualProfile⟩ :=
      CompatibleExpressionPrimitives.unary_source_types unique metadata.found form
        metadata.coercions metadata.requirements originalTyped
    exact ih childTyped
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualLeft, actualRight, actualMode, firstFound, secondFound, sameType, leftTyped, rightTyped, actualProfile⟩ :=
      CompatibleExpressionPrimitives.binary_source_types unique metadata.found form
        metadata.coercions metadata.requirements originalTyped
    exact ih leftTyped
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualLeft, actualRight, actualMode, firstFound, secondFound, sameType, leftTyped, rightTyped, actualProfile⟩ :=
      CompatibleExpressionPrimitives.binary_source_types unique metadata.found form
        metadata.coercions metadata.requirements originalTyped
    exact ih rightTyped
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualCondition, actualThen, actualElse, firstFound, secondFound, thirdFound,
        firstType, secondType, thirdType, conditionTyped, thenTyped, elseTyped⟩ :=
      CompatibleExpressionConditionals.conditional_source_types unique metadata.found form
        metadata.coercions originalTyped
    exact ih conditionTyped
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualCondition, actualThen, actualElse, firstFound, secondFound, thirdFound,
        firstType, secondType, thirdType, conditionTyped, thenTyped, elseTyped⟩ :=
      CompatibleExpressionConditionals.conditional_source_types unique metadata.found form
        metadata.coercions originalTyped
    exact ih thenTyped
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    have originalTyped := typed_at_lookup unique metadata.found typed
    obtain ⟨actualCondition, actualThen, actualElse, firstFound, secondFound, thirdFound,
        firstType, secondType, thirdType, conditionTyped, thenTyped, elseTyped⟩ :=
      CompatibleExpressionConditionals.conditional_source_types unique metadata.found form
        metadata.coercions originalTyped
    exact ih elseTyped

  | @index_base scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree inside ih =>
    have originalTyped := typed_at_lookup unique header.metadata.found typed
    obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types
      unique header.metadata.found form header.metadata.coercions originalTyped
    exact ih baseTyped
  | @index_key scope id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree inside ih =>
    have originalTyped := typed_at_lookup unique header.metadata.found typed
    obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types
      unique header.metadata.found form header.metadata.coercions originalTyped
    exact ih keyTyped

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodPathTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
/-! The actual accepted named body retains the same compiled terminal child.
Independent Source program typing authenticates that child's original raw
result type. The genuine parameter scope and production contextual compiler
construct its finite read/literal/group/pair receipt with literal sites. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {expression : ExpressionId}
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include terminal selected wellFormed in
/-- Complete original Source typing selects the same used terminal occurrence
and its raw result type at the actual parameter context. -/
theorem source_child :
    ∃ node, header.function.source.lookupExpression? expression = some node ∧
      node.type = header.function.resultType ∧
      ExpressionHasType header.function.source header.context expression node.type := by
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨final, facts, typed, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  rw [← stages.source selected] at typed
  obtain ⟨node, found, rawType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique
      (terminal.head child (stages.source selected)) typed complete
  rw [stages.source selected] at found childTyped
  exact ⟨node, found, rawType, childTyped⟩

include aligned terminal selected wellFormed in
/-- Accepted Header lowering constructs the actual finite child tree.
Ordinary catalog exclusions remain static Source metadata conditions. The
used code, result type and each literal site belong to the original callback. -/
theorem finite_child
    (ordinary : CompatibleExpressionProducts.Ordinary header.function.source
      compiled.indexed.base.locals (CallableIndexedNamedGeneration.context compiled.indexed prepared.named).owner)
    (syntaxTree : CompatibleExpressionProducts.Syntax header.function.source expression) :
    CompatibleExpressionProducts.Tree.WithLiterals
      (fuel := compiled.indexed.fuel)
      (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      (source := header.function.source) (context := header.context)
      (solved := header.solved) (reasonAt := header.reasonAt)
      (fun _ id lowered => CompatibleExpressionLiteralRuntime.Certificate header.solved header.function.source id lowered)
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression terminal.child := by
  obtain ⟨node, found, _rawType, typed⟩ := source_child terminal selected wellFormed
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry)
    (program := Program.ofChecked compiled.sourceProgram) header
  have accepted := terminal.generated
  have expressionPolicy : header.policy.lowerExpression =
      (RecursiveNamedPreparedHeaders.Prepared.policy prepared).lowerExpression :=
    congrArg SourceCoreLoops.Policy.lowerExpression aligned.policy
  rw [expressionPolicy] at accepted
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    prepared.compilation.parents prepared.compilation.own.assignments prepared.diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
    compiled.indexed.base.callableContext none none terminal.childFuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok terminal.child at accepted
  have tree := CallableIndexedOwnedPreparedStagedContextualProductReceipts.of_contextual
    (readFuel := compiled.indexed.fuel)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    ordinary header.unique declarations syntaxTree found typed rfl rfl rfl accepted
  simpa only [aligned.solved, CallableIndexedNamedGeneration.context, CompatibleNamedBody.bodyContext, RecursiveNamedCatalogNativeContexts.bodyScope] using tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
/-! A named body's static coverage retains the actual prepared Header and its
accepted compiler action. Terminal, lexical and branching statement receipts
share named entry, application and caller restoration. Branching receipts can
select canonical recursive expression support at the same original body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

inductive Compilation (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  | terminal (expression : ExpressionId)
      (receipt : Receipt header.policy header.fuel header.function.source
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
      (certificate : GenericExpressionMeaning.Certificate)
      (certifies : ∀ child,
        header.policy.lowerExpression receipt.childFuel header.function.source
          (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok child →
        certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression child)
  | lexical (receipt : CallableIndexedOwnedPreparedStagedNamedLexicalReceipts.Receipt header)
  | branching (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)
  | canonicalBranching (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)

structure Body (header : Header compiled (Program.ofChecked compiled.sourceProgram)) where
  row : SourceSpecialization.SpecializedFunction
  prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row
  instantiation : DeclarationInstantiation
  aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header
  layouts : header.layouts = compiled.indexed.layouts
  compilation : Compilation header

/-- Existing accepted terminal bodies retain their exact original receipt. -/
def of_terminal {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal header) : Body header :=
  ⟨terminal.row, terminal.prepared, terminal.instantiation, terminal.aligned, terminal.layouts,
    .terminal terminal.expression terminal.receipt terminal.certificate terminal.certifies⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedInvocationBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedInvocationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterMeaning CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedNamedEntryBounds (Prefix)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

include functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt in
/-- The actual Header and its authenticated named sidecar construct the body
scope. The native prefix reaches its real allocation state, where the body port
reconstructs the staged body. The original global application and the
literal restored caller are then constructed with its actual final lexical context. -/
theorem reflects_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) child faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (DataPatternValues.packValues payloads :: capture.captured) store
      (header.code.rename capture.embedding.lift) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨packet⟩ := CallableIndexedOwnedPreparedStagedNamedEntryBounds.native_prefix
    (functions := functions) (registry := registry) owner caller header capture sameLayouts member represented heaps completed
  let receipt := CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.parameter_receipt functions owner caller header capture packet stable heapTyped argumentsTyped
  have source := receipt.source wellFormed
  obtain ⟨sidecar, _issued, _same, globalSelected, _declaration, _local, _evidence, _return, _analysis⟩ :=
    CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.selected sourceAt prepared aligned stagePrepared descriptor
  have selected : (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function
      (RecursiveStageRegistry.scope sidecar [] header.function) := by
    rw [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] at globalSelected
    exact globalSelected
  have admitted : Admission poolBridge header.context packet.reached :=
    ⟨source.heapTyped, receipt.rows⟩
  obtain ⟨sourceSize, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld, trace, matched, result,
    finalHeaps, bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    children selected packet.entry.environments packet.entry.heaps packet.entry.locals
      packet.entry.lookups packet.entry.actualTyped packet.reached admitted owner
      (fun zero globals => receipt.packet zero globals)
      packet.completed (Nat.le_of_lt (Nat.lt_of_lt_of_le packet.strict within))
  have applied := CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.applies
    (caller := invocation) (context := context) sourceAt stagePrepared selected
    header.extended packet.entry.allocation trace matched
  have maps := packet.entry.maps.trans bodyMaps
  have worlds := packet.entry.worlds.trans bodyWorlds
  have frame := packet.entry.frame.trans bodyFrame
  have metadata := packet.entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := packet.related.trans bodyRelated
  have physical : (caller.rows owner.position).authority.frameLocation = keys[owner.position.val].frameLocation :=
    (caller.rows owner.position).frame_eq
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  have storeEq : finalStore = (CallableIndexedOwnedBodyRestoration.finalIndex (body :=
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
        finalMap, finalWorld, after, packet.bodyStore, packet.entry.canonical⟩) caller owner.position).store := by
    simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical] using packet.restored
  have whole := completed.sound
  rw [storeEq] at whole
  refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome, after, finalMap, finalWorld, applied, ?_⟩
  rw [storeEq]
  exact ⟨whole, result, restoredHeaps, maps, worlds, restoredFrame, metadata,
    CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position, restoredRelated, restoredPost⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedInvocationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceInversion
/-! A genuine nonempty method requirement list excludes primitive operation
rules. The remaining traces retain the actual selected dictionary and body,
including operand faults, parameter allocation and exact strict child grades. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceInversion
open Frontend SourceInference Staging.Recursive
open Solcore.SourceSemantics.Dynamic

inductive UnaryTrace (program : Program) (registry : Registry) (scope : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Heap)
    (operator : Syntax.UnaryOp) (operand : ExpressionId) (requirements : List RequirementId) :
    Nat → Outcome → Heap → Prop where
  | operandFault {operandSize after failure}
      (operandTrace : Size.Expression program registry operandSize scope context environment before operand (.fault failure) after) :
      UnaryTrace program registry scope context environment before operator operand requirements
        (Size.stepSize [operandSize]) (.fault failure) after
  | method {operandSize bodySize argumentsHeap bound after input traitName methodName bodyInstance dictionary
      roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
      (dispatch : UnaryTraitDispatch operator traitName methodName)
      (selection : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
      (operandTrace : Size.Expression program registry operandSize scope context environment before operand (.value input) argumentsHeap)
      (rootsEq : StatementRoots bodyInstance.source.roots roots)
      (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
      (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
      (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [input] bodyEnvironment bound)
      (body : Size.StatementsIn program registry true bodySize child bodyContext bodyEnvironment bound roots finalContext outcome after)
      (resultRule : BodyResult bodyInstance.resultType outcome result) :
      UnaryTrace program registry scope context environment before operator operand requirements
        (Size.stepSize [operandSize, bodySize]) result after

inductive BinaryTrace (program : Program) (registry : Registry) (scope : Scope)
    (context : Context) (environment : Dynamic.Environment) (before : Heap)
    (left : ExpressionId) (operator : Syntax.BinaryOp) (right : ExpressionId) (requirements : List RequirementId) :
    Nat → Outcome → Heap → Prop where
  | leftFault {leftSize after failure}
      (first : Size.Expression program registry leftSize scope context environment before left (.fault failure) after) :
      BinaryTrace program registry scope context environment before left operator right requirements
        (Size.stepSize [leftSize]) (.fault failure) after
  | rightFault {leftSize rightSize middle after input failure}
      (first : Size.Expression program registry leftSize scope context environment before left (.value input) middle)
      (continues : EvaluatesRightOperand operator input)
      (second : Size.Expression program registry rightSize scope context environment middle right (.fault failure) after) :
      BinaryTrace program registry scope context environment before left operator right requirements
        (Size.stepSize [leftSize, rightSize]) (.fault failure) after
  | method {leftSize rightSize bodySize middle argumentsHeap bound after a b traitName methodName bodyInstance dictionary
      roots child parameterTypes bodyContext finalContext bodyEnvironment outcome result}
      (dispatch : BinaryTraitDispatch operator traitName methodName)
      (selection : OperatorMethodSelected program context scope.evidence traitName methodName requirements bodyInstance dictionary)
      (first : Size.Expression program registry leftSize scope context environment before left (.value a) middle)
      (continues : EvaluatesRightOperand operator a)
      (second : Size.Expression program registry rightSize scope context environment middle right (.value b) argumentsHeap)
      (rootsEq : StatementRoots bodyInstance.source.roots roots)
      (selected : registry.Closure (methodView bodyInstance dictionary roots) child)
      (parameters : MonoBindersExtend bodyInstance.source.owner bodyInstance.context bodyInstance.source.inputs parameterTypes bodyContext)
      (allocate : BindersAllocate [] argumentsHeap bodyInstance.source.inputs [a, b] bodyEnvironment bound)
      (body : Size.StatementsIn program registry true bodySize child bodyContext bodyEnvironment bound roots finalContext outcome after)
      (resultRule : BodyResult bodyInstance.resultType outcome result) :
      BinaryTrace program registry scope context environment before left operator right requirements
        (Size.stepSize [leftSize, rightSize, bodySize]) result after

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context : Context} {environment : Dynamic.Environment} {before after : Heap}
  {id : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Outcome}

private theorem occurrence_form {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : actualForm = node.form := by
  obtain ⟨actualNode, contains, actualFormEq, _, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact actualFormEq.symm.trans (congrArg ExpressionNode.form same)

private theorem occurrence_requirements {actualForm : ExpressionForm} {requirements : List RequirementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (occurrence : Occurrence invocation id actualForm requirements) : node.requirements = requirements := by
  obtain ⟨actualNode, contains, _, actualRequirements, _⟩ := occurrence
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  exact (congrArg ExpressionNode.requirements same).symm.trans actualRequirements

theorem requirements_nonempty {caller : EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : BodyInstance} {dictionary : EvidenceEnvironment}
    (selected : OperatorMethodSelected program context caller traitName methodName requirements body dictionary) :
    requirements ≠ [] := by
  cases selected
  simp

theorem unary {operator : Syntax.UnaryOp} {operand : ExpressionId}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .unary operator operand) (nonempty : node.requirements ≠ [])
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    UnaryTrace program registry invocation context environment before operator operand node.requirements size outcome after := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .unary operator operand :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | unaryOperandFault occurrence operandTrace =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      exact .operandFault operandTrace
  | unaryMethod occurrence dispatch selection operandTrace rootsEq selected parameters allocate body resultRule =>
      obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (actual occurrence)
      rw [← occurrence_requirements unique found occurrence] at selection
      exact .method dispatch selection operandTrace rootsEq selected parameters allocate body resultRule
  | unary occurrence _ _ | unaryInvalid occurrence _ _ =>
      exact False.elim (nonempty (occurrence_requirements unique found occurrence))
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | tupleValue occurrence _ _ | tupleFault occurrence _ | constructorValue occurrence _ _ | constructorFault occurrence _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _ | binaryRightFault occurrence _ _ _ | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | binaryPanic occurrence _ _ _ _ | binaryMethod occurrence _ _ _ _ _ _ _ _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

theorem binary {left right : ExpressionId} {operator : Syntax.BinaryOp}
    (unique : NodeOccurrencesUnique invocation.source) (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .binary left operator right) (nonempty : node.requirements ≠ [])
    (trace : Size.Expression program registry size invocation context environment before id outcome after) :
    BinaryTrace program registry invocation context environment before left operator right node.requirements size outcome after := by
  have actual : ∀ {actualForm requirements}, Occurrence invocation id actualForm requirements → actualForm = .binary left operator right :=
    fun occurrence => (occurrence_form unique found occurrence).trans form
  cases trace with
  | generalizedLocal contains actualForm _ _ _ _ _ _ _
  | generalizedLocalRequirement contains actualForm _ _ _ _ _ _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      cases same
      rw [form] at actualForm
      cases actualForm
  | coercedValue contains _ raw _ | coercedFault contains _ raw =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      have shape := CallableIndexedOwnedPreparedStagedCoercionExclusion.raw_shape raw
      rw [same, form] at shape
      rcases shape with atomic | ⟨_, _, _, impossible⟩
      · cases atomic
      · cases impossible
  | atomicValue contains atomic _ _ | atomicFault contains atomic _ _ =>
      have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [same, form] at atomic
      cases atomic
  | binaryLeftFault occurrence first =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      exact .leftFault first
  | binaryRightFault occurrence first continues second =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      exact .rightFault first continues second
  | binaryMethod occurrence dispatch selection first continues second rootsEq selected parameters allocate body resultRule =>
      obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (actual occurrence)
      rw [← occurrence_requirements unique found occurrence] at selection
      exact .method dispatch selection first continues second rootsEq selected parameters allocate body resultRule
  | binaryLeftInvalid occurrence _ _ | binaryShortCircuit occurrence _ _ | binary occurrence _ _ _ _ | binaryInvalid occurrence _ _ _ _ | binaryPanic occurrence _ _ _ _ =>
      exact False.elim (nonempty (occurrence_requirements unique found occurrence))
  | group occurrence _ | pair occurrence _ _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _ | tupleValue occurrence _ _ | tupleFault occurrence _ | constructorValue occurrence _ _ | constructorFault occurrence _ | indexBaseFault occurrence _ | indexKeyFault occurrence _ _ | indexResult occurrence _ _ _ | unary occurrence _ _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _ | unaryMethod occurrence _ _ _ _ _ _ _ _ _ | conditional occurrence _ _ | conditionalFault occurrence _ | builtinArgumentsFault occurrence _ | builtinApplied occurrence _ _ | directArgumentsFault occurrence _ _ | directApplied occurrence _ _ _ _ _ | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _ | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _ | applied occurrence _ _ _ _ _ _ => cases actual occurrence

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedInvocationPreservation
/-! Authentic named parameter allocation and body preservation compose with
literal caller restoration. Body ports permit arbitrary final lexical Source
contexts while restoring the entry native scope and full caller admission. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedInvocationPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation (body_prefix)

section Native
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
private theorem rename_prefix (body : Expr) (ξ : Renaming) :
    body.rename (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)) =
      ((body.rename ξ).weakenAt 0).weakenAt 0 := by
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix]

private theorem next_evaluates (index : Int) (actual : Environment) (store : Store) (saved : Value) :
    Evaluates (saved :: actual) store
      ((SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index)).weakenAt 0)
      (encode compiled.indexed.ancestry.layout.frame (.state index)) store := by
  rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
  exact CallableIndexedContextFrames.literal_evaluates _ _ _ _

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include functions owner caller header capture sourceAt in
/-- Authentic Source allocation and the strict staged body child construct the
native parameter/body continuation before literal caller restoration. The
returned state retains full representation, relates and caller PostAdmission. -/
theorem preserves_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context heap (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
    exact original.locals
  have liveReference : capture.canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.reference
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨childSize, child, environment, bound, finalContext, bodyOutcome,
    selected, allocated, bodyTrace, converted, smaller⟩ := body_prefix sourceAt wellFormed arity trace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift))
      (DataPatternValues.packValues payloads :: capture.canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift capture.layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped capture.typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame model :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys model
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      model owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), capture.canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement⟩ := parameters_with_state installedAuthority
    capture.environments liveLocals liveReference capture.coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner caller header arguments :=
    ⟨origin, index, metadata, capture.administrative, _,
      .unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: capture.captured,
      Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) capture.embedding.lift),
      authority.frameLocation, (caller.rows owner.position).frame_eq, owned, history, emitted,
      entry, parameterState, installedRelated.trans parameterRelated, stable, heapTyped, argumentsTyped⟩
  have admitted : Admission poolBridge header.context parameterState := ⟨(receipt.source wellFormed).heapTyped, receipt.rows⟩
  obtain ⟨value, bodyStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
    bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyState, bodyRelated, bodyPost⟩ :=
    children selected entry.environments entry.heaps entry.locals entry.lookups
      entry.actualTyped parameterState admitted owner
      (fun zero globals => receipt.packet zero globals)
      bodyTrace converted (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  have prefixEvaluation := agreement.wrap bodyEvaluation
  rw [rename_prefix] at prefixEvaluation
  have reference : (DataPatternValues.packValues payloads :: capture.captured)[capture.embedding.lift
      (compiled.indexed.base.globals.length + 1)]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ, physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using capture.capturedReference
  have evaluation := CallableContextFrames.withFrame_evaluates (.var reference) authority.frame.read
    (next_evaluates index (DataPatternValues.packValues payloads :: capture.captured) store
      (encode compiled.indexed.ancestry.layout.frame authority.current)) prefixEvaluation
  have renamed : header.code.rename capture.embedding.lift = withFrame
      (.var (capture.embedding.lift (compiled.indexed.base.globals.length + 1)))
      (SourceCoreCallableIndexedDispatch.literal compiled.indexed.ancestry.layout.frame (.state index))
      (header.parameterCode.rename capture.embedding.lift) := by
    rw [emitted, NamedCalls.withFrame_rename, Expr.rename, CallableIndexedRenaming.literal]
  have maps := entry.maps.trans bodyMaps
  have worlds := entry.worlds.trans bodyWorlds
  have frame := entry.frame.trans bodyFrame
  have sourceMetadata := entry.metadata.trans bodyMetadata
  have related : Relates caller bodyState := installedRelated.trans (parameterRelated.trans bodyRelated)
  obtain ⟨restoredHeaps, restoredFrame, _cell, _fromBody, restoredRelated, _records, _transition⟩ :=
    CallableIndexedOwnedBodyRestoration.restore_return caller bodyState owner.position header.registered finalHeaps worlds
      (by simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using frame) related
  have restoredPost := CallableIndexedOwnedPreparedStagedBodyRestorationAdmission.restore_post
    caller bodyState owner.position stable bodyPost supports restoredFrame
  refine ⟨value, _, finalMap, finalWorld, ?_, result, restoredHeaps, maps, worlds,
    restoredFrame, sourceMetadata, CallableIndexedOwnedBodyRestoration.returned caller bodyState owner.position,
    restoredRelated, restoredPost⟩
  simpa only [CallableIndexedOwnedBodyRestoration.finalIndex, ← physical, authority] using
    (renamed.symm ▸ evaluation)
end Native
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedInvocationPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedApplicationBounds
/-! The complete retained named carrier applies its literal native closure.
The real apply rule gives the invocation its strict native grade. The original
staged Source application and exact returned caller pool remain independent of
that grade; the invocation producers retain nested stage failure identity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header mapping world)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

open CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds (carrier)

include functions owner caller header capture sourceAt in
/-- Source allocation and its selected body construct the exact invocation,
then the physical payload apply rule. No native grade is equated to Source. -/
theorem application_preserves
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptor : Word) (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages
      size invocation context before (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [carrier (owner := owner) header capture identity descriptor, DataPatternValues.packValues payloads]
        store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨value, finalStore, finalMap, finalWorld, result⟩ :=
    CallableIndexedOwnedPreparedStagedNamedInvocationPreservation.preserves_invocation
      functions owner caller header capture sourceAt sameLayouts member wellFormed
      stable heapTyped argumentsTyped represented heaps supports budget children trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) result.1, result⟩

variable {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named header.named.signature.key))

include functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt in
/-- The actual complete native apply supplies a strict body invocation grade.
Its original Header and authenticated staged scope then construct the Source
application, with the exact full postcondition in the returned caller pool. -/
theorem application_reflects
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (member : header ∈ headers)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    (represented : CallableIndexedParameterMeaning.Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    (supports : Dynamic.TypeContextSupports header.context context)
    (identity descriptorWord : Word) (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        child faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [carrier (owner := owner) header capture identity descriptorWord, DataPatternValues.packValues payloads]
      store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context before
        (.global function) arguments outcome after ∧
      Evaluates [carrier (owner := owner) header capture identity descriptorWord, DataPatternValues.packValues payloads]
        store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
        (registry := registry) (payloads := payloads) functions owner caller header capture
        context outcome after value finalStore finalMap finalWorld faults := by
  obtain ⟨bodySize, smaller, invoked⟩ := completed.apply_body
    (.second (.first (.var rfl))) (.var rfl)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ :=
    CallableIndexedOwnedPreparedStagedNamedInvocationBounds.reflects_invocation
      functions owner caller header capture prepared aligned stagePrepared descriptor sourceAt
      sameLayouts member wellFormed stable heapTyped argumentsTyped represented heaps supports budget children
      invoked (Nat.le_trans (Nat.le_of_lt smaller) within)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, completed.sound, result⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedParentBounds
/-! The actual named Header, original selected caller row and raw successful
argument trace feed the literal terminal application. Its returned pool is
restored around the original caller. The Source and native grades remain
independent, and nested stage failures retain their original scope and call.
Static named compiler provenance and strict expression coverage are inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry} {faults : RecursiveStageMeaning.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {mapping argumentMap : LocationMap} {world argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution} {function : Dynamic.GlobalFunction}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.global function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (callerPrepared : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.global function))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (calleeHeapTyped : Dynamic.HeapWellTyped context calleeHeap)
  (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.global function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (capture : NamedCapture headers owner.key header argumentMap argumentWorld)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  (sourceAt : NamedSourceAt header rawD function)
  (identity descriptorWord : Word)
  (carrierEq : carrier = CallableIndexedOwnedPreparedStagedTerminalNamedApplicationBounds.carrier
    (owner := owner) header capture identity descriptorWord)
  (nativeType : compiler.calleeCode.type =
    CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
  (sameLayouts : header.layouts = compiled.indexed.layouts)
  (member : header ∈ headers)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)

include profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
  calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt nativeType in
private theorem arguments_at {argumentsSize : Nat}
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap) :
    CallableIndexedParameterMeaning.Arguments model argumentMap argumentWorld header.bindings sources values ∧
    Dynamic.HeapWellTyped header.function.context argumentsHeap ∧
    Dynamic.ValuesHaveTypes header.function.context argumentsHeap sources header.types ∧
    Dynamic.TypeContextSupports header.context context ∧
    compiler.original.type = header.function.resultType ∧ lowered.type = header.output := by
  have secondAccepted : CallableContract.decision prepared.site.gates .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract = none := by
    rw [prepared.site.decision_known .beforeApplication
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown dispatch.contract dispatch.row dispatch.found]
    exact SourceCoreCallableContracts.reason_accepted dispatch.row prepared.site.reasonAt .beforeApplication
      (dispatch.row.afterArguments_ok (count.trans selected.argument_count.symm))
  obtain ⟨parameters, physicalArity, rawResult⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.accepted_rows sourceAt compiler wellFormed
      actualFunctionType callerPrepared dispatch selected secondAccepted calleeTyped nativeType represented bundle
  obtain ⟨headerHeap, headerArguments, supports⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.at_successful_arguments sourceAt wellFormed
      runtime covers locals calleeHeapTyped typing calleeTyped bundle physicalArity argumentsTrace
  have callable := compiler.callableType
  rw [actualFunctionType] at callable
  have nativeSignature := CallableIndexedOwnedStoredNativePackReceipts.callable_parameters (callable.trans nativeType)
  have sameCore : lowered.type = header.output :=
    (congrArg (fun output => output.type) compiler.output).trans
      (compiler.resultTypeEq.symm.trans (nativeSignature.2.trans header.resultType))
  exact ⟨parameters, headerHeap, headerArguments, supports, originalResult.trans rawResult, sameCore⟩

include bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture in
private theorem restored_result {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {value : Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    (sameSource : compiler.original.type = header.function.resultType)
    (sameCore : lowered.type = header.output)
    (resultAt : CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
      (registry := registry) (payloads := values) functions owner (bridge.pool reached) header capture
      context outcome after value finalStore finalMap finalWorld faults) :
    RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
      finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
    ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      callerProtocol.Relates initial returned ∧
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
        compiler.original.type outcome returned := by
  obtain ⟨_invoked, resultRep, finalHeaps, applicationMaps, applicationWorlds, applicationFrame,
    applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ := resultAt
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type faults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers locals calleeHeapTyped
  typing calleeTyped actualFunctionType represented bundle originalResult owner header capture sourceAt
  identity descriptorWord carrierEq nativeType sameLayouts member in
/-- The original Source global application supplies allocation and its selected
terminal body once. The native suffix and all three original binds then join
the real callee and ordered argument effects into the whole caller result. -/
theorem preserves_parent (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child faults budget)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.global function) sources outcome after)
    (within : applicationSize ≤ budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
      calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt
      nativeType argumentsTrace
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedNamedApplicationBounds.application_preserves
      functions owner (bridge.pool reached) header capture sourceAt sameLayouts member wellFormed
      admitted.rows headerHeap headerArguments parameters heaps supports identity descriptorWord budget children called within
  rw [← carrierEq] at application
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps, finalMaps, finalWorlds,
    finalFrame, finalMetadata, returned, relatedFinal, post⟩

variable {row : SourceSpecialization.SpecializedFunction}
  (namedPrepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt namedPrepared instantiation header)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
  (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
    (.named header.named.signature.key))
  (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)

include bridge profile compiler prepared sourceParent occurrence initial reached related admitted heaps maps worlds
  frame heapMetadata dispatch selected callerPrepared count accepted wellFormed runtime covers locals calleeHeapTyped
  typing calleeTyped actualFunctionType represented bundle originalResult owner header capture sourceAt
  identity descriptorWord carrierEq nativeType sameLayouts member namedPrepared aligned
  stagePrepared descriptor stageEq in
/-- The real accepted suffix gives a strict measured application. Original
named registry authority then constructs the actual Source application, and
the returned pool supplies the full original parent's caller postcondition. -/
theorem reflects_suffix (budget : Nat)
    (children : ∀ {child : Staging.Recursive.Scope},
      (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        child faults budget)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.global function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨parameters, headerHeap, headerArguments, supports, sameSource, sameCore⟩ :=
    arguments_at profile compiler prepared dispatch selected callerPrepared count wellFormed runtime covers locals
      calleeHeapTyped typing calleeTyped actualFunctionType represented bundle originalResult header sourceAt
      nativeType argumentsTrace
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  rw [carrierEq] at application
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, _wholeApplication, resultAt⟩ :=
    CallableIndexedOwnedPreparedStagedNamedApplicationBounds.application_reflects
      functions owner (bridge.pool reached) header capture sourceAt
      namedPrepared aligned stagePrepared descriptor sameLayouts member wellFormed admitted.rows headerHeap headerArguments
      parameters heaps supports identity descriptorWord budget children application (Nat.le_of_lt strict)
  have called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSourceSize
      invocation context argumentsHeap (.global function) sources outcome after := by
    simpa only [stageEq] using applied
  obtain ⟨parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩ :=
    restored_result bridge profile compiler initial reached related maps worlds frame heapMetadata owner header capture
      sameSource sameCore resultAt
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize], outcome, after,
    finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    parentRep, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, returned, relatedFinal, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts
/-! Existing terminal receipts supply the general named body ports. The
adapter makes their unchanged Source context explicit; lexical body receipts
can supply a different final context through the same invocation interface. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)} {expression : ExpressionId}
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)


include selected wellFormed terminal certifies in
theorem preserves (budget : Nat)
    (children : CallableIndexedOwnedPreparedStagedNamedChildBounds.PreservesBelow
      (headers := headers) (keys := keys) header model stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner packet size finalContext bodyOutcome
    outcome after trace matched within
  exact CallableIndexedOwnedPreparedStagedNamedChildBounds.preserves_body
    selected wellFormed terminal certifies environments heaps locals agrees typed initial admitted owner packet
    budget children trace matched within

include selected wellFormed terminal certifies in
theorem reflects (budget : Nat)
    (children : CallableIndexedOwnedPreparedStagedNamedChildBounds.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child certificate faults budget) :
    CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header model stages child faults budget := by
  intro mapping world administrative actualContext environment canonical actual before store ξ
    environments heaps locals agrees typed initial admitted owner packet size value finalStore completed within
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, result⟩ :=
    CallableIndexedOwnedPreparedStagedNamedChildBounds.reflects_body
      selected wellFormed terminal certifies environments heaps locals agrees typed initial admitted owner packet
      budget children completed within
  exact ⟨sourceSize, header.context, _, outcome, after, finalMap, finalWorld, trace, matched, result⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyPorts
end
