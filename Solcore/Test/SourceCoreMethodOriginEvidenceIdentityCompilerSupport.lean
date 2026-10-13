import Solcore.Test.SourceCoreMethodOriginEvidenceMetadata
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedReturningExpressionAdmission

/-! The two existing identity bodies are recovered from their accepted return
and read actions, using the same finite metadata table as the other roots. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open AcceptedNamedExpressionFlow

variable {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
  {type : TypeSystem.Ty} {row : ObservedRow fixture signature}
  (shape : SelectedIdentityShape row.row.function type)

theorem ActualHeader.identity_compiler_admission
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed row.named row.row.function.typedBody (DirectSite directRows))
    (supported : ∀ instantiation, DirectSite directRows instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported
        fixture.recipe.compiled.indexed.base.plan instantiation) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header directRows := by
  have bodyEq : actual.header.function.body = [shape.statement.id] := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have namedEq : actual.prepared.named = row.named :=
    CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.cached_named actual.prepared row.cached row.same
  have actualMetadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
      fixture.recipe.compiled.indexed actual.prepared.named actual.header.function.source (DirectSite directRows) := by
    rw [namedEq, actual.source]
    exact metadata
  have onlyRead : ∀ id node, actual.header.function.source.lookupExpression? id = some node →
      node = shape.read.node := by
    intro id node found
    rw [actual.source] at found
    exact shape.expression nodes found
  have noDirect : ∀ id node, actual.header.function.source.lookupExpression? id = some node →
      ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) → False := by
    intro id node found callee arguments instantiation form
    rw [onlyRead id node found, shape.read.form] at form
    cases form
  exact AcceptedNamedBodyExpressionAdmission.of_returning actual.prepared actual.aligned actualMetadata
    supported (fun id node found callee arguments instantiation form =>
      False.elim (noDirect id node found callee arguments instantiation form))
    bodyEq (by rw [actual.source]; exact shape.statementFound) shape.statementForm
    (reached := fun _ => True) (by
      intro id node _ found
      rw [onlyRead id node found]
      exact .inl (shape.read.form ▸ LeafForm.read _ _))
    (fun id _ initializer => by
      obtain ⟨initializer⟩ := initializer
      have found := initializer.found
      simp only [noLocals, List.find?_nil, Option.filter_none] at found
      cases found)
    (by
      intro id node _ found callee arguments instantiation form argument member
      exact False.elim (noDirect id node found callee arguments instantiation form))
    True.intro fixture.source_wellFormed

end Tests.SourceCoreMethodOriginEvidence
