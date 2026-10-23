import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedInitializer
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalLambdaMetadata
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalMetadata
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLocalOrigins

/-! The real initializer's ordered compiler receipts supply its indexed rows.
Candidate metadata and source origins come from the actual compiled catalog;
no body profile or future execution is required to create the same bundle. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationInitializerRows
open Core Frontend SourceInference TypeSystem SourceCoreLocalPolymorphism
open GeneralizedLocalInstanceCompilation (Inputs)
open DataPatternValues

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {inputs : Inputs} {binding : Binding} {active : Substitution}
  {binder : Resolved.LocalId}
  (located : compiled.indexed.base.locals.binding inputs.current.owner binder = .ok binding)
  (initializer : inputs.initializer = binding.initializer)
  (represented : inputs.representation =
    (CallableIndexedNamedGeneration.representation compiled.indexed).atContext inputs.current.owner active)
  (program : inputs.program = compiled.indexed.base.sourceProgram)
  (locals : inputs.locals = compiled.indexed.base.locals)
  (native : inputs.native = compiled.indexed.base.callableContext)
  (plan : inputs.current.plan = compiled.indexed.base.plan)
  (globals : inputs.current.globals = compiled.indexed.base.globals)
  (administrativePrefix : inputs.current.administrativePrefix = 1)

include located initializer represented in
private theorem actual_packet {candidate : Instance} {raw : Core.Expr}
    (member : candidate ∈ binding.atContext active)
    (receipt : GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw) :
    Nonempty (GeneralizedLocalLambdaCompilation.Packet inputs candidate raw) := by
  have metadata := (SelectedCompilationLocalMetadata.at_context compiled located member).2.2
  have origin := SelectedCompilationLocalOrigins.at_context compiled located member
  obtain ⟨_sourceOwner, _binderOwner, _initializerOwner, node, parameters, result, body,
      found, form, _sourceType, _functionType, _closed, _parameterType, _resultType⟩ := metadata
  have initial : candidate.origin.initializer = inputs.initializer := origin.2.2.2.trans initializer.symm
  rw [initial] at found
  have source := GeneralizedLocalLambdaEmissionFacts.Emission.source receipt.emission
  have reader : inputs.representation.expressions.readExpression =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked := by
    rw [represented]
    rfl
  exact GeneralizedLocalLambdaMetadata.packet_of_compatible receipt reader (source ▸ found) form

include located initializer represented program locals native plan globals administrativePrefix in
/-- Every actual row retains its own packet and full cumulative native key.
The order is the production mapM order, even for equal native function types. -/
theorem indexed_rows {candidates : List Instance} {closures : List Core.Expr}
    (members : ∀ candidate ∈ candidates, candidate ∈ binding.atContext active)
    (rows : ListRel (fun candidate raw => Nonempty
      (GeneralizedLocalInstanceCompilation.Receipt inputs candidate raw)) candidates closures) :
    GeneralizedLocalAcceptedInitializer.IndexedRows compiled.indexed inputs active candidates closures := by
  induction rows with
  | nil => exact .nil
  | @cons candidate raw rest remaining head tail ih =>
    have member := members candidate (by simp)
    obtain ⟨receipt⟩ := head
    obtain ⟨packet⟩ := actual_packet compiled located initializer represented member receipt
    have caller := (SelectedCompilationLocalOrigins.at_context compiled located member).1.symm
    obtain ⟨indexed⟩ := GeneralizedLocalLambdaGeneration.of_packet compiled.indexed packet active
      represented program locals native plan caller globals administrativePrefix
    let exactIndexed : GeneralizedLocalLambdaGeneration.Indexed compiled.indexed packet :=
      { indexed with lexical := active, represented := represented }
    exact .cons ⟨⟨packet, exactIndexed, rfl⟩⟩
      (ih (fun candidate member => members candidate (List.mem_cons_of_mem _ member)))

include located initializer represented program locals native plan globals administrativePrefix in
/-- A successful actual initializer and its literal compiler input fields
produce the existing full accepted-bundle receipt, including an empty bundle. -/
theorem of_receipt {lowered : SourceCoreBasic.LoweredExpr}
    (original : GeneralizedLocalInitializerCompilation.Receipt inputs binding active lowered) :
    Nonempty (GeneralizedLocalAcceptedInitializer.Receipt compiled.indexed inputs binding active lowered) := by
  refine ⟨⟨original, indexed_rows compiled located initializer represented program locals native plan globals
    administrativePrefix (fun _ member => member) original.rows, ?_, ?_⟩⟩
  · intro candidate member
    exact (SelectedCompilationLocalOrigins.at_context compiled located member).2.1
  · intro candidate member
    exact congrArg TypedBinder.id (SelectedCompilationLocalOrigins.at_context compiled located member).2.2.1

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationInitializerRows
