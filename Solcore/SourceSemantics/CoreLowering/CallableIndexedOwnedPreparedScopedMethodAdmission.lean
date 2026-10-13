import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodBodies

/-! Actual cached method sources are checked for scoped declaration calls.
Selected principals retain their full evidence and exact SourceAt context. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedMethodAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots (DirectSource)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← allProof? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

private def DirectForm (form : ExpressionForm) : Prop :=
  (∃ name resolution, form = .reference name resolution) ∨
  (∃ callee arguments instantiation, form = .call callee arguments (.declaration instantiation))

private def directNode? (node : SourceInference.Node) :
    Option (PLift (∀ expression, node = .expression expression → DirectForm expression.form)) :=
  match node with
  | .statement _ => some ⟨by intro expression impossible; cases impossible⟩
  | .expression expression =>
    match form : expression.form with
    | .reference name resolution =>
      some ⟨by intro actual same; cases same; exact .inl ⟨name, resolution, form⟩⟩
    | .call callee arguments (.declaration instantiation) =>
      some ⟨by intro actual same; cases same; exact .inr ⟨callee, arguments, instantiation, form⟩⟩
    | _ => none

def directSource? (source : TypedSource) : Option (PLift (DirectSource source)) := do
  let ⟨all⟩ ← allProof? (fun node => ∀ expression, node = .expression expression → DirectForm expression.form)
    directNode? source.nodes
  pure ⟨by intro id node found; exact all _ (lookupExpression?_sound found).1 node rfl⟩

structure SourceCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction) : Type where
  forms : DirectSource (CallableIndexedNamedGeneration.source named)
  source : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission compiled named
    (CallableIndexedNamedGeneration.source named) (statements (CallableIndexedNamedGeneration.source named))
    named.specialized.function.inferredBodyType directRows

def certifySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (fuel : Nat) : Option (SourceCertificate compiled named directRows) := do
  let ⟨forms⟩ ← directSource? (CallableIndexedNamedGeneration.source named)
  let ⟨source⟩ ← CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource compiled named
    (CallableIndexedNamedGeneration.source named) (statements (CallableIndexedNamedGeneration.source named))
    named.specialized.function.inferredBodyType directRows fuel
  pure ⟨forms, source⟩

def Excluded (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Prop :=
  ∀ definition ∈ (Program.ofChecked compiled.sourceProgram).methods,
    named.specialized.function.typedBody.owner ≠ definition.body.source.owner

def RowCase (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction) : Prop :=
  Excluded compiled named ∨ Nonempty (SourceCertificate compiled named directRows)

structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (directRows : List SourceSpecialization.SpecializedFunction) : Type where
  rows : ∀ named ∈ compiled.indexed.base.functions, RowCase compiled named directRows

/-- A method-owned cache row must pass the original source check. Unrelated
owners are excluded by the complete original method definition table. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (Certificate compiled directRows) := do
  let ⟨rows⟩ ← allProof? (fun named => RowCase compiled named directRows)
    (fun named =>
      if excluded : (Program.ofChecked compiled.sourceProgram).methods.all
          (fun definition => decide (named.specialized.function.typedBody.owner ≠ definition.body.source.owner)) = true then
        some ⟨Or.inl (fun definition member =>
          of_decide_eq_true (List.all_eq_true.mp excluded definition member))⟩
      else do
        let source ← certifySource compiled named directRows fuel
        pure ⟨Or.inr ⟨source⟩⟩) compiled.indexed.base.functions
  pure ⟨rows⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {directRows : List SourceSpecialization.SpecializedFunction}
  (certificate : Certificate compiled directRows)
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)

include certificate in
theorem Certificate.selected : Nonempty (SourceCertificate compiled principal.named directRows) := by
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
    ⟨name, resolution, read⟩ | ⟨callee, arguments, instantiation, read⟩ <;>
    rw [read] at form <;> cases form

include certificate in
/-- Genuine method selection supplies the resolved caller internally to the
program issuer. The certificate supplies static Source syntax and metadata. -/
theorem Certificate.support
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (resolved : CallableIndexedOwnedPreparedStagedDirectCallAuthority.ResolvedCaller
      compiled.sourceProgram principal.named.specialized principal.dictionary)
    (diagnostic : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt principal.cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {inputs : List (Input compiled)} (rows : Inventory inputs) (aligned : TableAligned inputs directRows)
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (stages : Staging.Recursive.Registry) :
    ∃ packet : CallableIndexedOwnedPreparedStagedMethodBodies.Packet principal,
      packet.sourceAt = sourceAt ∧ CallableIndexedOwnedPreparedStagedMethodBodies.Support
        principal packet (headers rows) stages
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  obtain ⟨source⟩ := certificate.selected principal
  have roots : statements (CallableIndexedNamedGeneration.source principal.named) = principal.cached.compilation.statements := by
    rw [principal.source_eq]
    exact principal.source_frame.roots.filterMap_eq
  have resultType : principal.named.specialized.function.inferredBodyType = principal.sourceBody.resultType := by
    rw [principal.cached.same]
    rfl
  have shape := source.source.body.shape
  rw [roots, principal.source_eq] at shape
  have accepted := sourceAt.accepted principal.cached.compilation
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  let packet : CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.Packet principal :=
    ⟨sourceAt, flow, generated, (Except.ok.inj returned).symm, shape⟩
  refine ⟨.scoped packet, rfl, ?_⟩
  apply CallableIndexedOwnedPreparedStagedMethodEvidenceScopedRoots.of_actual_with_evidence
    (directSites := DirectSite directRows)
    principal packet diagnostic receiver wellFormed
    (by simpa only [principal.source_eq] using source.forms)
    (fun _ site => site.supported aligned)
    (by simpa only [principal.source_eq] using source.source.metadata)
    rows (fun _ site _ _ target global => site.covered rows aligned target global)
    resolved ready member
  obtain ⟨final, facts, typed, _complete⟩ :=
    CallableIndexedOwnedPreparedStagedMethodScopedStaticSupport.statements principal packet wellFormed
  have body := source.source.body
  rw [roots, principal.source_eq, resultType] at body
  exact body.syntax sourceAt.unique typed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedMethodAdmission
