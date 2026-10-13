import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveSourceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport

/-! A finite check of the actual cache supplies terminal primitive method
packets. Original method selection, Source typing and the full dictionary come
from each genuine principal and SourceAt receipt, independently of this check. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveMethodAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport (PrimitiveSource)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)

structure SourceCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) where
  expression : ExpressionId
  terminal : Terminal (CallableIndexedNamedGeneration.source named) expression
    (statements (CallableIndexedNamedGeneration.source named))
  forms : PrimitiveSource (CallableIndexedNamedGeneration.source named)
  metadata : MetadataFor compiled.indexed named (CallableIndexedNamedGeneration.source named) (fun _ => False)
  tree : GeneralSyntax (CallableIndexedNamedGeneration.source named) expression (fun _ => False)

/-- This first certificate accepts an original terminal return and its primitive
expression graph. It checks all lookupable expression metadata in the source. -/
def certifySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (fuel : Nat) : Option (SourceCertificate compiled named) := do
  let source := CallableIndexedNamedGeneration.source named
  let ⟨forms⟩ ← CallableIndexedOwnedPreparedPrimitiveSourceAdmission.primitiveSource? source
  let ⟨metadata⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata? compiled.indexed named source (fun _ => False)
  match roots : statements source with
  | [] => none
  | first :: rest =>
      match found : source.lookupStatement? first with
      | none => none
      | some node =>
          match form : node.form with
          | .returnStmt (some expression) => do
              let ⟨tree⟩ ← CallableIndexedOwnedPreparedPrimitiveSourceAdmission.expression? source fuel expression
              pure {
                expression := expression
                forms := forms
                metadata := metadata
                tree := tree
                terminal := by
                  rw [roots]
                  exact .returning rest found form }
          | _ => none

def Excluded (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Prop :=
  ∀ definition ∈ (Program.ofChecked compiled.sourceProgram).methods,
    named.specialized.function.typedBody.owner ≠ definition.body.source.owner

def RowCase (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Prop :=
  Excluded compiled named ∨ Nonempty (SourceCertificate compiled named)

/-- Every actual cached row is either proved unrelated to a method owner or
has a checked source certificate. This is additional static certification. -/
structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled) : Type where
  rows : ∀ named ∈ compiled.indexed.base.functions, RowCase compiled named

private def certifyRows (compiled : SourceCoreUnifiedCompilation.Compiled) (fuel : Nat) :
    (rows : List SourceCoreGeneralFunctions.Function) → Option (PLift (∀ named ∈ rows, RowCase compiled named))
  | [] => some ⟨by intro named impossible; cases impossible⟩
  | first :: rest => do
      let ⟨head⟩ ← (if excluded : (Program.ofChecked compiled.sourceProgram).methods.all
          (fun definition => decide (first.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
        some ⟨Or.inl (by
          intro definition member
          exact of_decide_eq_true (List.all_eq_true.mp excluded definition member))⟩
        else do
          let certificate ← certifySource compiled first fuel
          pure ⟨Or.inr ⟨certificate⟩⟩ : Option (PLift (RowCase compiled first)))
      let ⟨tail⟩ ← certifyRows compiled fuel rest
      pure ⟨by
        intro named member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail named member⟩

def certify (compiled : SourceCoreUnifiedCompilation.Compiled) (fuel : Nat) : Option (Certificate compiled) := do
  let ⟨rows⟩ ← certifyRows compiled fuel compiled.indexed.base.functions
  pure ⟨rows⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled} (certificate : Certificate compiled)
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)

include certificate in
/-- The real cached selection and original method instantiation exclude the
unrelated-owner case, without a comparison with a fixture-selected method. -/
theorem Certificate.selected : Nonempty (SourceCertificate compiled principal.named) := by
  rcases certificate.rows principal.named (List.mem_of_getElem? principal.cached.selected) with excluded | source
  · obtain ⟨implementation, declaration, trait, definition, substitution, instantiated⟩ := principal.source_instantiation
    cases instantiated with
    | intro _ _ _ _ definitionMember _ _ _ _ source _ _ =>
      have selectedOwner : principal.sourceBody.source.owner = definition.body.source.owner := by
        rw [source]
        rfl
      have namedOwner : principal.named.specialized.function.typedBody.owner = principal.sourceBody.source.owner := by
        rw [principal.cached.same]
        rfl
      exact False.elim (excluded definition definitionMember (namedOwner.trans selectedOwner))
  · exact source

include certificate in
theorem Certificate.no_lambda
    {id : ExpressionId} {node : ExpressionNode} {parameters : List TypedBinder}
    {resultType : TypeSystem.Ty} {body : List StatementId}
    (found : principal.sourceBody.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters resultType body) : False := by
  obtain ⟨source⟩ := certificate.selected principal
  rw [← principal.source_eq] at found
  rcases source.forms id node found with
    ⟨name, resolution, read⟩ | ⟨spelling, resolution, read⟩ | ⟨condition, first, second, read⟩ <;>
    rw [read] at form <;> cases form

include certificate in
/-- SourceAt fixes the original method context, evidence and body typing. The
actual accepted compiler action issues the static packet used by the family. -/
theorem Certificate.support
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal,
      packet.sourceAt = sourceAt ∧ CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Support
        principal packet headers stages (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨source⟩ := certificate.selected principal
  have roots : statements (CallableIndexedNamedGeneration.source principal.named) = principal.cached.compilation.statements := by
    rw [principal.source_eq]
    exact principal.source_frame.roots.filterMap_eq
  have terminal := source.terminal
  rw [roots, principal.source_eq] at terminal
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rfl) terminal sourceAt.accepted
  let packet : CallableIndexedOwnedPreparedStagedMethodBodyStaticSupport.Packet principal :=
    ⟨sourceAt, source.expression, receipt⟩
  refine ⟨packet, rfl, ?_⟩
  apply CallableIndexedOwnedPreparedStagedPrimitiveMethodTerminalSupport.of_actual principal packet diagnostic receiver wellFormed
  · simpa only [principal.source_eq] using source.forms
  · simpa only [principal.source_eq] using source.metadata
  · simpa only [principal.source_eq] using source.tree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveMethodAdmission
