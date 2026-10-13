import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows

/-! The original coerced declaration call retains its raw input/result typing
and full evidence partition. Argument execution uses the original Source scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectArguments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedRawDirectAuthority (Port EvidenceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {fuel : Nat}
  {invocation : Staging.Recursive.Scope} {scope : SourceCoreBasic.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    child fuel invocation.source scope id callee ids instantiation reasonAt callables node output)
  (port : Port receipt headers)
  {context : SourceSemantics.Context}
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)

include receipt in
theorem source_types (unique : NodeOccurrencesUnique invocation.source)
    (typed : ExpressionHasType invocation.source context id node.type) :
    ∃ types, DirectDeclarationCalleeValid context invocation.source callee instantiation ∧
      DeclarationApplicationValid context instantiation types node.rawType instantiation.predicates ∧
      ExpressionsHaveTypes invocation.source context ids types := by
  generalize reportedEq : node.type = reported at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw rawEq _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans receipt.found)
    subst actualNode
    rw [← rawEq, receipt.form] at raw
    cases raw with
    | directCall calleeValid application argumentsTyped =>
      cases application with
      | intro signatureMember admissible declaration parameters result functionType predicates =>
        exact ⟨_, calleeValid, .intro signatureMember admissible declaration parameters result functionType rfl,
          argumentsTyped⟩

include receipt in
theorem children {stages : Staging.Recursive.Registry} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {size : Nat} {outcome : Staging.Recursive.Outcome}
    (trace : Staging.Recursive.Size.RawForm (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before node.form node.requirements node.coercions outcome after) :
    (∃ sequenceSize invocationSize argumentsHeap values name evidence,
      size = Staging.Recursive.Size.stepSize [sequenceSize, invocationSize] ∧
      Staging.Recursive.Occurrence invocation callee (.reference name (.declaration instantiation)) ∧
      SourceSemantics.DeclarationInstantiation.Valid context instantiation ∧
      Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages sequenceSize
        invocation context environment before ids (.values values) argumentsHeap ∧
      Dynamic.DirectCallProducesEvidence context invocation.evidence node.requirements node.coercions
        instantiation.predicates evidence ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages invocationSize
        invocation context argumentsHeap (.global ⟨instantiation,evidence⟩) values outcome after) ∨
    (∃ sequenceSize failure, size = Staging.Recursive.Size.stepSize [sequenceSize] ∧ outcome = .fault failure ∧
      Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages sequenceSize
        invocation context environment before ids (.fault failure) after) := by
  rw [receipt.form] at trace
  cases trace with
  | rawAtomicValue atomic _ | rawAtomicFault atomic _ => cases atomic
  | rawDirectApplied occurrence valid children produced invoked =>
      exact .inl ⟨_,_,_,_,_,_,rfl,occurrence,valid,children,produced,invoked⟩
  | rawDirectArgumentsFault _ children => exact .inr ⟨_,_,rfl,rfl,children⟩

include port in
theorem callee_receipt
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (calleeValid : DirectDeclarationCalleeValid context invocation.source callee instantiation) :
    ∃ name, Staging.Recursive.Occurrence invocation callee (.reference name (.declaration instantiation)) ∧
      SourceSemantics.DeclarationInstantiation.Valid context instantiation := by
  cases calleeValid with
  | intro contains form admissible _ requirements coercions =>
    refine ⟨_, ⟨_, contains, form, requirements, coercions⟩,
      CompatibleSourceInstantiationClosure.declaration_valid admissible runtime.variables_closed
        port.supported.ranges⟩

include receipt port evidenceAt in
theorem global_eq {evidence : Dynamic.EvidenceEnvironment}
    (produced : Dynamic.DirectCallProducesEvidence context invocation.evidence node.requirements node.coercions
      instantiation.predicates evidence) :
    Dynamic.Value.global ⟨instantiation, evidence⟩ = .global port.function := by
  have same := evidenceAt.agrees evidence produced
  have metadata := port.sourceInstantiation
  cases h : port.function with
  | mk actual actualEvidence =>
    simp only [h] at metadata same ⊢
    cases metadata
    cases same
    rfl

section Successful
variable {stages : Staging.Recursive.Registry} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {sourceTypes : List TypeSystem.Ty}
  {arguments : List Dynamic.Value} {payloads : List Value}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping}

include receipt port evidenceAt in
theorem at_successful_arguments
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (calleeValid : DirectDeclarationCalleeValid context invocation.source callee instantiation)
    (application : DeclarationApplicationValid context instantiation sourceTypes
      node.rawType instantiation.predicates)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before ids (.values arguments) after)
    (represented : DataExpressionSequence.Values model mapping world
      (port.header.bindings.map (fun binding => binding.1.scheme.body))
      (receipt.loweredArguments.map (·.type)) arguments payloads)
    (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.header.bindings arguments payloads ∧
      Dynamic.HeapWellTyped port.header.function.context after ∧
      Dynamic.ValuesHaveTypes port.header.function.context after arguments port.header.types ∧
      Dynamic.TypeContextSupports port.header.context context := by
  obtain ⟨_, _, valid⟩ := callee_receipt receipt port runtime calleeValid
  have functionType : instantiation.type = .function (TypeSystem.Ty.productMany sourceTypes) node.rawType := by
    cases application with
    | intro _ _ _ _ _ functionType _ => exact functionType
  have calleeTyped : Dynamic.ValueHasType context before (.global port.function)
      (.function (TypeSystem.Ty.productMany sourceTypes) node.rawType) := by
    have portValid : SourceSemantics.DeclarationInstantiation.Valid context port.function.instantiation := by
      simpa only [port.sourceInstantiation] using valid
    have portCovers : port.function.evidence.Covers
        ((SourceSemantics.Context.ofSignatures context.signatures).withAssumptions
          port.function.instantiation.predicates) := by
      have produced := evidenceAt.produces
      cases produced with
      | intro _ _ produces =>
        constructor
        · exact produces.valid
        · simpa only [port.sourceInstantiation, SourceSemantics.Context.withAssumptions,
            Dynamic.EvidenceEnvironment.Supplies] using produces.supplies
    have base := Dynamic.ValueHasType.global (heap := before) portValid portCovers
    simpa only [port.sourceInstantiation, functionType] using base
  have binderCount : arguments.length = port.header.bindings.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have arity : port.header.function.parameters.length = arguments.length := by
    rw [port.header.parameters, List.length_map, binderCount]
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.loweredArguments.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.header.bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.loweredArguments).symm.trans
      (receipt.native.inputType.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.header.parameterType))
  have representedRows := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.header.bindings represented binderCount rfl nativePacked
  obtain ⟨bodyHeap, bodyArguments, supports⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.at_successful_arguments port.sourceAt
      wellFormed runtime covers locals heapTyped typing calleeTyped rfl arity trace
  exact ⟨representedRows, bodyHeap, bodyArguments, supports⟩
end Successful
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectArguments
