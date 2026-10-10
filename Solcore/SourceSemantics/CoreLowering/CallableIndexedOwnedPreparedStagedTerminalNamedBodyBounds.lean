import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds

/-! The original prepared named Header supplies the accepted terminal compiler
receipt. Independent Source program typing determines the used terminal child
at the Header's real parameter context. Strict expression hypotheses establish
both staged body directions at the same actual reached parameter state,
retaining nested stage failures and the full pool post. Native parameter entry
and caller restoration remain separate producers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt Terminal)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {expression : ExpressionId}

include aligned in
/-- The actual original body callback, its read policy and terminal Source
occurrence construct this receipt; a second body compilation is not assumed. -/
theorem compiler_receipt
    (terminal : Terminal header.function.source expression header.function.body) :
    Nonempty (Receipt header.policy header.fuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body) :=
  CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (RecursiveNamedPreparedHeaderPolicies.Prepared.header_read prepared aligned) terminal aligned.accepted

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
  (selected : stages.Closure header.function child)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (terminal : Receipt header.policy header.fuel header.function.source
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
    expression header.function.body header.output header.reasonAt header.fellThrough header.escaped header.body)
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  (certifies : ∀ lowered,
    header.policy.lowerExpression terminal.childFuel header.function.source
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression header.reasonAt = .ok lowered →
    certificate (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) expression lowered)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative
    (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before header.context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State
    ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge header.context initial)

include selected wellFormed terminal certifies environments heaps locals agrees typed admitted in
/-- The original named body Source typing and genuine selected child scope
construct preservation from the used strict expression hypothesis. The body
trace and nested failure scope remain recursively staged. -/
theorem preserves_body (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge header.context model stages child certificate faults budget)
    {size : Nat} {finalContext : SourceSemantics.Context} {bodyOutcome : Staging.Recursive.BodyOutcome}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages size child
      header.context environment before header.function.body finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult header.function.resultType bodyOutcome outcome)
    (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (header.body.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  rw [← stages.source selected] at bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.preserves_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := bodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children trace matched within

include selected wellFormed terminal certifies environments heaps locals agrees typed admitted in
/-- Literal native body completion reflects to an independently graded staged
Source body, using the same accepted Header code and actual parameter state.
The complete returned pool and successful Source post are retained. -/
theorem reflects_body (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge header.context model stages child certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (header.body.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize child
        header.context environment before header.function.body header.context
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) after ∧
      Staging.Recursive.BodyResult header.function.resultType
        (CallableIndexedOwnedAdmittedStagedTerminalStatements.control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        header.function.resultType header.output faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State
          ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)),
            finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge header.context header.function.resultType outcome reached := by
  have view : LambdaMetadataViews.MetadataView child.source header.function.source := by
    rw [stages.source selected]
    exact .refl _
  have unique : NodeOccurrencesUnique child.source := by
    rw [stages.source selected]
    exact header.unique
  obtain ⟨staticFinal, facts, bodyTyped, complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  rw [← stages.source selected] at bodyTyped
  exact CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.reflects_body
    (receipt := terminal) (view := view) (bridge := bridge) (bodyTyped := bodyTyped) (complete := complete)
    (certifies := certifies) (environments := environments) (heaps := heaps) (locals := locals)
    (agrees := agrees) (typed := typed) (initial := initial) (admitted := admitted)
    unique budget children completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedBodyBounds
