import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows

/-! Direct declaration calls retain the independently typed Source argument
row. Empty actual declaration substitution and predicates recover callable
validity and its exact dictionary; authentic compiler bundles align native
arguments only after the Source row supplies physical arity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {invocation : Staging.Recursive.Scope} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values invocation.source scope id callee ids
    instantiation reasonAt lowered)
  (port : Port receipt headers)
  {context : SourceSemantics.Context}

include receipt in
theorem callee_receipt
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (calleeValid : DirectDeclarationCalleeValid context invocation.source callee instantiation) :
    ∃ name, Staging.Recursive.Occurrence invocation callee (.reference name (.declaration instantiation)) ∧
      SourceSemantics.DeclarationInstantiation.Valid context instantiation := by
  cases calleeValid with
  | intro contains form admissible _ requirements coercions =>
    refine ⟨_, ⟨_, contains, form, requirements, coercions⟩,
      CompatibleSourceInstantiationClosure.declaration_valid admissible runtime.variables_closed ?_⟩
    intro parameter replacement member
    rw [receipt.monomorphic.substitution] at member
    cases member

include receipt in
theorem evidence_eq_empty {evidence : Dynamic.EvidenceEnvironment}
    (produced : Dynamic.DirectCallProducesEvidence context invocation.evidence [] []
      instantiation.predicates evidence) : evidence = [] := by
  cases produced with
  | intro _ _ produces =>
    have length := produces.length_eq.2
    rw [receipt.monomorphic.predicates] at length
    exact List.length_eq_zero_iff.mp length.symm

include receipt in
theorem empty_evidence (context : SourceSemantics.Context)
    (caller : Dynamic.EvidenceEnvironment) :
    Dynamic.DirectCallProducesEvidence context caller [] [] instantiation.predicates [] := by
  rw [receipt.monomorphic.predicates]
  exact .intro (selected := []) (contextual := []) rfl rfl .nil

include receipt port in
theorem global_eq {evidence : Dynamic.EvidenceEnvironment}
    (produced : Dynamic.DirectCallProducesEvidence context invocation.evidence [] []
      instantiation.predicates evidence) :
    Dynamic.Value.global ⟨instantiation, evidence⟩ = .global port.function := by
  have empty := evidence_eq_empty receipt produced
  have metadata := port.sourceInstantiation
  have dictionary := port.sourceEvidence
  cases h : port.function with
  | mk actual actualEvidence =>
    simp only [h] at metadata dictionary ⊢
    cases metadata
    cases dictionary
    cases empty
    rfl

section Successful
variable {stages : Staging.Recursive.Registry} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {sourceTypes : List TypeSystem.Ty}
  {arguments : List Dynamic.Value} {payloads : List Value}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping}

include receipt port in
theorem at_successful_arguments
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (calleeValid : DirectDeclarationCalleeValid context invocation.source callee instantiation)
    (application : DeclarationApplicationValid context instantiation sourceTypes
      receipt.node.type instantiation.predicates)
    {size : Nat}
    (trace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before ids (.values arguments) after)
    (represented : DataExpressionSequence.Values model mapping world
      (port.header.bindings.map (fun binding => binding.1.scheme.body))
      (receipt.codes.map (·.type)) arguments payloads)
    (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.header.bindings arguments payloads ∧
      Dynamic.HeapWellTyped port.header.function.context after ∧
      Dynamic.ValuesHaveTypes port.header.function.context after arguments port.header.types ∧
      Dynamic.TypeContextSupports port.header.context context := by
  obtain ⟨_, _, valid⟩ := callee_receipt receipt runtime calleeValid
  have functionType : instantiation.type = .function (TypeSystem.Ty.productMany sourceTypes) receipt.node.type := by
    cases application with
    | intro _ _ _ _ _ functionType _ => exact functionType
  have calleeTyped : Dynamic.ValueHasType context before (.global port.function)
      (.function (TypeSystem.Ty.productMany sourceTypes) receipt.node.type) := by
    have portValid : SourceSemantics.DeclarationInstantiation.Valid context port.function.instantiation := by
      simpa only [port.sourceInstantiation] using valid
    have portCovers : port.function.evidence.Covers
        ((SourceSemantics.Context.ofSignatures context.signatures).withAssumptions
          port.function.instantiation.predicates) := by
      rw [port.sourceEvidence, port.sourceInstantiation, receipt.monomorphic.predicates]
      constructor
      · intro goal evidence found
        cases found
      · intro predicate member
        cases member
    have base := Dynamic.ValueHasType.global (heap := before) portValid portCovers
    simpa only [port.sourceInstantiation, functionType] using base
  have binderCount : arguments.length = port.header.bindings.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have arity : port.header.function.parameters.length = arguments.length := by
    rw [port.header.parameters, List.length_map, binderCount]
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.header.bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.codes).symm.trans
      (receipt.parameter.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.header.parameterType))
  have representedRows := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.header.bindings represented binderCount rfl nativePacked
  obtain ⟨bodyHeap, bodyArguments, supports⟩ :=
    CallableIndexedOwnedPreparedStagedNamedArgumentRows.at_successful_arguments port.sourceAt
      wellFormed runtime covers locals heapTyped typing calleeTyped rfl arity trace
  exact ⟨representedRows, bodyHeap, bodyArguments, supports⟩
end Successful
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectArgumentRows
