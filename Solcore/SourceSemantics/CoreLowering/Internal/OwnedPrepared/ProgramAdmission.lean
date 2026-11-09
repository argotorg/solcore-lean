import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.PreparedBranching
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ScopedSourceBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodSelection
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodScopedRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalMixedFamilies
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.CoercionSpine
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedLambdaFormation

/-!
# Prepared callables: program admission

Admission of programs, methods and scoped factories, and physical program support.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
/-! The original returned lambda retains its scoped statement certificate.
The compiler producer derives this certificate from its accepted inner body;
physical formation uses the same original source and captured state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

structure SourceCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (body : List StatementId) where
  expression : ExpressionId
  terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal source expression body
  node : ExpressionNode
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  reported : Core.Ty
  found : source.lookupExpression? expression = some node
  form : node.form = .lambda parameters result statements
  owner : expression.occurrence.owner = source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
    source expression = .ok (node, reported)
  scan : ScopedSourceBodyAdmission.Scan source (fun _ => True) result true statements
  bareUnary : PreparedBranchingBareUnarySyntax.Body source statements

abbrev Certificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) :=
  SourceCertificate compiled named named.specialized.function.typedBody
    (statements named.specialized.function.typedBody)

/-- The original uniform-error API retains its original bare assignment shape. -/
structure LegacySourceCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (body : List StatementId) extends SourceCertificate compiled named source body where
  shape : CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape source true statements

abbrev LegacyCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) :=
  LegacySourceCertificate compiled named named.specialized.function.typedBody
    (statements named.specialized.function.typedBody)

/-- Actual cached identity transports the source certificate to the exact
Header and its compiled statement roots. -/
def at_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) (certificate : Certificate compiled named) :
    SourceCertificate compiled prepared.named header.function.source header.function.body := by
  obtain ⟨source, body, _result⟩ := header_data prepared aligned
  rw [source, body, cached_named prepared selected same]
  exact certificate

def legacy_at_header {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) (certificate : LegacyCertificate compiled named) :
    LegacySourceCertificate compiled prepared.named header.function.source header.function.body := by
  obtain ⟨source, body, _result⟩ := header_data prepared aligned
  rw [source, body, cached_named prepared selected same]
  exact certificate

/-- The terminal compiler receipt and its Point are constructed here. No
caller supplies expression syntax, metadata or a closure execution premise. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (same : named.specialized = row) (certificate : LegacyCertificate compiled named)
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
    {semanticFaults : FunctionCalls.FaultRep}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → semanticFaults reason token) :
    ∃ terminal : Terminal header,
      Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
        (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal) := by
  let source := legacy_at_header prepared aligned selected same certificate
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (by rw [aligned.policy]; rfl) source.terminal aligned.accepted
  let terminal : Terminal header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, expression := source.expression, receipt := receipt,
    certificate := CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) source.expression receipt.child,
    certifies := by
      intro child generated
      have childEq : child = receipt.child := Except.ok.inj (generated.symm.trans receipt.generated)
      exact ⟨rfl, rfl, childEq⟩ }
  exact ⟨terminal, CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors.of_branching terminal
    ready diagnostic receiver included wellFormed profile member source.found source.form source.owner
    source.requirements source.coercions source.ordinary source.read source.shape
    (fun typed => (source.scan.syntax header.unique rfl typed).legacy source.shape) rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedFactoryAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginsMethodAdmission
/-! Finite checks retain generic implementation parameters and complete method
predicates. The final compiler table supplies authentic evidence origins. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginsMethodAdmission
open Core Frontend SourceInference

structure ImplementationFormation (implementation : ProgramImplementationSignature) : Prop where
  parameters : implementation.parameters.Nodup
  variables : TypedTraitResolution.predicateVariables implementation.head = []
  headParameters : ∀ parameter ∈ TypedTraitResolution.predicateParameters implementation.head,
    parameter ∈ implementation.parameters
  methodParameters : ∀ method ∈ implementation.methods, ∀ predicate ∈ method.wherePredicates,
    ∀ parameter ∈ TypedTraitResolution.predicateParameters predicate, parameter ∈ implementation.parameters

theorem ImplementationFormation.formed {implementation : ProgramImplementationSignature}
    (formation : ImplementationFormation implementation) {method : ProgramImplMethodSignature}
    (member : method ∈ implementation.methods) :
    CallableCoercionMethodInstantiation.Formation implementation method := by
  refine ⟨formation.parameters, ?_, ?_, ?_⟩
  · intro metavariable occurs
    have present := TypedTraitResolution.mem_predicateVariables_iff.mpr occurs
    rw [formation.variables] at present
    cases present
  · intro parameter occurs
    exact formation.headParameters parameter (TypedTraitResolution.mem_predicateParameters_iff.mpr occurs)
  · intro predicate present parameter occurs
    exact formation.methodParameters method member predicate present parameter
      (TypedTraitResolution.mem_predicateParameters_iff.mpr occurs)

def implementation? (implementation : ProgramImplementationSignature) :
    Option (PLift (ImplementationFormation implementation)) :=
  if parameters : implementation.parameters.Nodup then
    if variables : TypedTraitResolution.predicateVariables implementation.head = [] then
      if head : (TypedTraitResolution.predicateParameters implementation.head).all
          (fun parameter => decide (parameter ∈ implementation.parameters)) = true then
        if methods : implementation.methods.all (fun method => method.wherePredicates.all
            (fun predicate => (TypedTraitResolution.predicateParameters predicate).all
              (fun parameter => decide (parameter ∈ implementation.parameters)))) = true then
          some ⟨⟨parameters, variables,
            fun parameter member => of_decide_eq_true (List.all_eq_true.mp head parameter member),
            by
              intro method member predicate present parameter occurs
              exact of_decide_eq_true (List.all_eq_true.mp
                (List.all_eq_true.mp (List.all_eq_true.mp methods method member) predicate present)
                parameter occurs)⟩⟩
        else none
      else none
    else none
  else none

def implementations? : (implementations : List ProgramImplementationSignature) →
    Option (PLift (∀ implementation ∈ implementations, ImplementationFormation implementation))
  | [] => some ⟨by intro implementation member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← implementation? first
      let ⟨tail⟩ ← implementations? rest
      pure ⟨by
        intro implementation member
        rcases List.mem_cons.mp member with same | member
        · exact same ▸ head
        · exact tail implementation member⟩

/-- The original finite signatures and actual final specialization table are
checked independently of any execution or Source typing assumption. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Option (PLift (CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled)) := do
  let ⟨formed⟩ ← implementations? compiled.sourceProgram.signatures.implementations
  let ⟨ready⟩ ← CallableMethodOriginTable.validate compiled.sourceProgram
    compiled.indexed.base.plan.specializations
  pure ⟨⟨⟨fun implementation member _method methodMember =>
    (formed implementation member).formed methodMember⟩, ready⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOriginsMethodAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedMethodAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrimitiveMethodAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
/-! Static coverage of the actual named, closure and method bodies supplies both
semantic directions at every reached public receiver. A successful compilation
does not by itself supply this coverage. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)

theorem stagePrepared (compiled : SourceCoreUnifiedCompilation.Compiled) :
    RecursiveNamedPreparedStageContracts.Prepared compiled
      compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected

def stages (compiled : SourceCoreUnifiedCompilation.Compiled) : Staging.Recursive.Registry :=
  RecursiveNamedPreparedStageScopes.registry (stagePrepared compiled)

/-- Every support field retains an actual compiler packet or original Source.
The body laws follow from the closed physical family below. -/
structure Support (compiled : SourceCoreUnifiedCompilation.Compiled)
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed) where
  profile : compiled.compatible.checked.catalog.callableContracts = true
  wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)
  issued : IssuedAt compiled.indexed initial.entry initial.result.context.registry
    initial.result.extension initial.result.diagnostics
  registry : initial.result.context.registry = compiled.compatible.checked.staticRegistry
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program
  bodies : ∀ header, header ∈ headers → CallableIndexedOwnedPreparedStagedNamedBodies.Body header
  bodySupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
      (headers := headers) (bodyRegistry := initial.result.context.registry)
      (stages := stages compiled)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      header (bodies header member)
  closurePackets : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys
      initial.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.PacketFor association.original (stages compiled)
  closureSupport : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association headers keys
      initial.result.context.registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SupportFor association.original
      (stages compiled) (closurePackets association)
  owners : ∀ owner : OwnedKey keys, CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers
  methods : CallableIndexedOwnedPreparedStagedPhysicalMixedCallerFamily.MixedMethodSupports
    (compiled := compiled) (headers := headers) (stages := stages compiled)
    (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}

def functions (support : Support compiled headers keys initial) :=
  CallableIndexedOwnedPhysicalCellOrigins.functions headers keys initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics) support.profile

theorem observations (support : Support compiled headers keys initial) :
    CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
      (functions support) (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro metadata mapping world sourceType source native type origin
  exact CallableIndexedOwnedGeneralLambdaValues.observations _ initial.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
    support.profile (registry := metadata)
    (CallableIndexedOwnedPhysicalCellOrigins.functions_include_general support.profile origin)

variable {receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : Support compiled headers keys initial)
  (issued : IssuedAt compiled.indexed receiving.entry receiving.result.context.registry
    receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)

include support extension in
theorem static_extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    receiving.result.context.registry := by
  change SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry _
  rw [← support.registry]
  exact extension

include support issued extension in
theorem semantic_extension : ∀ reason token,
    CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics (.semantic reason) token := by
  obtain ⟨program, present⟩ := support.diagnostics
  intro reason token represented
  exact CompatibleRegistryDiagnosticExtension.semantic_preserved compiled
    support.issued issued present extension represented

include support issued extension in
theorem preserves_bodies (header) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.PreservesBelow
      (headers := headers) (keys := keys) header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support))
      (stages compiled) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  exact
    haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
      (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled support.issued)
    CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.preserves_with_methods
      issued (stagePrepared compiled) support.profile support.wellFormed (observations support)
      (static_extension support extension) (semantic_extension support issued extension)
      support.bodies support.bodySupport support.closurePackets support.closureSupport support.owners support.methods
      header member selected budget

include support issued extension in
theorem reflects_bodies (header) (member : header ∈ headers)
    {child : Staging.Recursive.Scope} (selected : (stages compiled).Closure header.function child) (budget : Nat) :
    CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts.ReflectsBelow
      (headers := headers) (keys := keys) header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry (functions support))
      (stages compiled) child (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) budget := by
  exact
    haveI := CallableIndexedOwnedPublicDecodedCallFaults.tokens
      (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled support.issued)
    CallableIndexedOwnedPreparedStagedPhysicalMixedNamedFamilyPorts.reflects_with_methods
      issued (stagePrepared compiled) support.profile support.wellFormed (observations support)
      (static_extension support extension) (semantic_extension support issued extension)
      support.bodies support.bodySupport support.closurePackets support.closureSupport support.owners support.methods
      rfl header member selected budget

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
/-! One finite certificate checks actual cached roots, original lambda bodies,
method sources and coercion selection. Its issuer constructs the shared static
program support; independent Source well-formedness remains explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (TableAligned)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport (statements)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedPreparedPhysicalProgramSupport (stagePrepared stages Support)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog)

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

inductive RootCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction) where
  | scoped (source : CallableIndexedOwnedPreparedNamedScopedAdmission.SourceAdmission
      compiled named named.specialized.function.typedBody (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows)
  | formation (source : CallableIndexedOwnedPreparedNamedFactoryAdmission.Certificate compiled named)
  | scopedFactory (source : CallableIndexedOwnedPreparedScopedFactoryAdmission.LegacyCertificate compiled named)
  | excluded (absent : ∀ signature ∈ compiled.sourceProgram.signatures.functions,
      named.specialized.declaration ≠ signature.id)

def certifyRoot (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (fuel : Nat) : Option (RootCertificate compiled named directRows) :=
  match CallableIndexedOwnedPreparedNamedScopedAdmission.admitSource compiled named
      named.specialized.function.typedBody (statements named.specialized.function.typedBody)
      named.specialized.function.inferredBodyType directRows fuel with
  | some ⟨source⟩ => some (.scoped source)
  | none =>
    match CallableIndexedOwnedPreparedNamedFactoryAdmission.certifyCachedFactory compiled named with
    | some source => some (.formation source)
    | none =>
      if absent : compiled.sourceProgram.signatures.functions.all (fun signature =>
          decide (named.specialized.declaration ≠ signature.id)) = true then
        some (.excluded (fun signature member => of_decide_eq_true (List.all_eq_true.mp absent signature member)))
      else none

inductive Selection (compiled : SourceCoreUnifiedCompilation.Compiled)
    (directRows : List SourceSpecialization.SpecializedFunction) where
  | closed (methods : CallableIndexedOwnedPreparedPrimitiveMethodAdmission.Certificate compiled)
      (catalog : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog compiled)
  | origins (methods : CallableIndexedOwnedPreparedScopedMethodAdmission.Certificate compiled directRows)
      (catalog : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog compiled)

def Selection.allowCoerced {compiled : SourceCoreUnifiedCompilation.Compiled}
    {directRows : List SourceSpecialization.SpecializedFunction} : Selection compiled directRows → Bool
  | .closed .. => true
  | .origins .. => false

def Selection.operatorCatalog {compiled : SourceCoreUnifiedCompilation.Compiled}
    {directRows : List SourceSpecialization.SpecializedFunction} :
    Selection compiled directRows → CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled
  | .closed _ catalog => .generic ⟨catalog.formed, catalog.assumptions⟩
  | .origins _ catalog => .origins catalog

def certifySelection (compiled : SourceCoreUnifiedCompilation.Compiled)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (Selection compiled directRows) :=
  let closed := do
    let methods ← CallableIndexedOwnedPreparedPrimitiveMethodAdmission.certify compiled fuel
    let ⟨catalog⟩ ← CallableIndexedOwnedPreparedClosedCoercionAdmission.certify compiled
    pure (.closed methods catalog)
  match closed with
  | some selection => some selection
  | none => do
    let methods ← CallableIndexedOwnedPreparedScopedMethodAdmission.certify compiled directRows fuel
    let ⟨catalog⟩ ← CallableIndexedOwnedPreparedOriginsMethodAdmission.certify compiled
    pure (.origins methods catalog)

structure RowCertificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) where
  root : RootCertificate compiled named directRows
  closures : CallableIndexedOwnedPreparedClosureAdmission.SourceCertificate compiled named directRows allowCoerced

def certifyRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (directRows : List SourceSpecialization.SpecializedFunction)
    (allowCoerced : Bool) (fuel : Nat) : Option (RowCertificate compiled named directRows allowCoerced) := do
  let root ← certifyRoot compiled named directRows fuel
  let ⟨closures⟩ ← CallableIndexedOwnedPreparedClosureAdmission.certifySource compiled named directRows allowCoerced fuel
  pure ⟨root, closures⟩

structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled) where
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  selection : Selection compiled table.rows
  rows : ∀ named ∈ compiled.indexed.base.functions,
    Nonempty (RowCertificate compiled named table.rows selection.allowCoerced)
  profile : compiled.compatible.checked.catalog.callableContracts = true
  diagnostics : ∃ program, compiled.indexed.base.diagnostics = some program

/-- A rejected row rejects the whole certificate. The direct-site table may
omit unused rows, but every actual cached source still receives a root check. -/
def certify (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (fuel : Nat) : Option (Certificate compiled) := do
  if profile : compiled.compatible.checked.catalog.callableContracts = true then
    match present : compiled.indexed.base.diagnostics with
    | none => none
    | some diagnostics =>
      let table := CallableIndexedOwnedPreparedOrdinarySyntaxTable.collect compiled wellFormed fuel
      let selection ← certifySelection compiled table.rows fuel
      let ⟨rows⟩ ← allProof? (fun named => Nonempty (RowCertificate compiled named table.rows selection.allowCoerced))
        (fun named => do
          let certificate ← certifyRow compiled named table.rows selection.allowCoerced fuel
          pure ⟨⟨certificate⟩⟩) compiled.indexed.base.functions
      pure ⟨table, selection, rows, profile, diagnostics, present⟩
  else none

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (certificate : Certificate compiled)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {recipe : SourceCoreIndexedSession.Recipe} (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  (checked : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
  (identity : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed initial.entry
    initial.result.context.registry initial.result.extension initial.result.diagnostics)
  (registry : initial.result.context.registry = compiled.compatible.checked.staticRegistry)
  {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (entryMember : entry ∈ compiled.indexed.entries)
  {inputs : List (Input compiled)} (rows : Inventory inputs)
  (aligned : TableAligned inputs certificate.table.rows)

include certificate wellFormed ready checked identity issued entryMember rows aligned in
theorem Certificate.named_support (input : Input compiled) (packet : Issued input) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body packet.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := initial.result.context.registry)
        (stages := stages compiled)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
        packet.header body) := by
  obtain ⟨source⟩ := certificate.rows input.prepared.named (List.mem_of_getElem? input.prepared.selected)
  let prepared := CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected
  have diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared :=
    ⟨packet.selected.diagnostics, packet.selected.found, rfl⟩
  cases source.root with
  | «scoped» admission =>
    have original := CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.source_at_header
      prepared packet.aligned input.prepared.selected input.prepared.same admission
    exact CallableIndexedOwnedPreparedNamedScopedAdmission.of_actual prepared packet.aligned rows aligned
      original ready diagnostic issued wellFormed checked identity
      certificate.selection.operatorCatalog
      entryMember (stagePrepared compiled)
  | formation admission =>
    obtain ⟨terminal, ⟨supported⟩⟩ := CallableIndexedOwnedPreparedNamedFactoryAdmission.of_actual
      prepared packet.aligned input.prepared.selected input.prepared.same admission ready diagnostic
      wellFormed certificate.profile entryMember
    exact ⟨⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal,
      .formation terminal supported packet.aligned.globals⟩⟩
  | scopedFactory admission =>
    obtain ⟨terminal, ⟨supported⟩⟩ := CallableIndexedOwnedPreparedScopedFactoryAdmission.of_actual
      prepared packet.aligned input.prepared.selected input.prepared.same admission ready diagnostic
      wellFormed certificate.profile entryMember issued (fun _ _ represented => represented)
    exact ⟨⟨CallableIndexedOwnedPreparedStagedNamedBodies.of_terminal terminal,
      .formation terminal supported packet.aligned.globals⟩⟩
  | excluded absent =>
    obtain ⟨request, signature, generic, member, _genericMember, _resolved, specialized⟩ := input.prepared.origin
    have fields := RecursiveNamedSpecializationBodyFacts.identities specialized
    have declaration : input.prepared.named.specialized.declaration = signature.id :=
      (congrArg (·.declaration) input.prepared.same).trans (fields.2.2.trans fields.1.symm)
    exact False.elim (absent signature member declaration)

include certificate wellFormed checked identity issued rows aligned in
theorem Certificate.closure_support
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association (headers rows) (keys compiled)
      initial.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.PacketFor
        association.original (stages compiled),
      CallableIndexedOwnedPreparedStagedPhysicalClosureStaticSupport.SupportFor association.original
        (stages compiled) packet) := by
  rcases association with ⟨original, _slots⟩
  cases original with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    obtain ⟨source⟩ := certificate.rows support.caller.named (List.mem_of_getElem? support.caller.selected)
    have found := code.sourceFound
    rw [support.source] at found
    obtain ⟨body⟩ := source.closures.selected found code.sourceForm
    cases body with
    | ordinary body =>
      obtain ⟨⟨packet, supported⟩⟩ := CallableIndexedOwnedPreparedClosureAdmission.of_ordinary
        (stagePrepared compiled) code support provenance issued wellFormed rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.terminal packet, supported⟩⟩
    | «scoped» body =>
      obtain ⟨⟨packet, supported⟩⟩ := CallableIndexedOwnedPreparedScopedClosureAdmission.of_actual
        (stagePrepared compiled) code support provenance issued wellFormed rows aligned checked identity
        certificate.selection.operatorCatalog body
      exact ⟨⟨.branching packet, supported⟩⟩
    | coerced enabled body =>
      cases selectionEq : certificate.selection with
      | closed methods catalog =>
        obtain ⟨⟨packet, supported⟩⟩ := CallableIndexedOwnedPreparedCoercedClosureAdmission.of_actual
          (stagePrepared compiled) code support provenance issued wellFormed rows aligned checked identity
          catalog body
          (fun principal sourceAt diagnostic => methods.support principal sourceAt diagnostic issued wellFormed
            (headers := headers rows) (stages compiled))
        exact ⟨⟨.terminal packet, supported⟩⟩
      | origins methods catalog =>
        simp only [selectionEq, Selection.allowCoerced, Bool.false_eq_true] at enabled
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    have found := code.sourceFound
    rw [support.source, support.principal.source_eq] at found
    cases certificate.selection with
    | closed methods _ => exact False.elim (methods.no_lambda support.principal found code.sourceForm)
    | origins methods _ => exact False.elim (methods.no_lambda support.principal found code.sourceForm)

private theorem owners_physical (rows : Inventory inputs) :
    ∀ selected : CallableIndexedOwnedFunctionValues.OwnedKey (keys compiled),
      CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical selected.key (headers rows) := by
  intro selected
  have same : selected = CallableIndexedOwnedPreparedBootstrapRootState.owner compiled := by
    cases selected with
    | mk position =>
      have samePosition : position = (CallableIndexedOwnedPreparedBootstrapRootState.owner compiled).position := by
        apply Fin.ext
        have bound := position.isLt
        change position.val < 1 at bound
        change position.val = 0
        omega
      cases samePosition
      rfl
  rw [same]
  exact CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _

include certificate wellFormed ready checked identity issued registry entryMember rows aligned in
/-- Finite raw-row alignment is the only inventory adapter. All three semantic
families are issued internally from the single original-source certificate. -/
theorem Certificate.issue_for :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) := by
  have named : ∀ header, header ∈ headers rows →
      Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
        CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
          (headers := headers rows) (bodyRegistry := initial.result.context.registry)
          (stages := stages compiled)
          (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
          header body) := by
    intro header member
    obtain ⟨input, packet, _retained, same⟩ := rows.mem_headers header member
    cases same
    exact certificate.named_support wellFormed ready checked identity issued entryMember rows aligned input packet
  let namedChoice := fun header member => Classical.choice (named header member)
  let closureChoice := fun {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedPhysicalClosureAssociation.Association (headers rows) (keys compiled)
      initial.result.context.registry (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      mapping world function native bindings parameter result) =>
    Classical.choice (certificate.closure_support wellFormed checked identity issued rows aligned association)
  refine ⟨{
    profile := certificate.profile
    wellFormed := wellFormed
    issued := issued
    registry := registry
    diagnostics := certificate.diagnostics
    bodies := fun header member => (namedChoice header member).1
    bodySupport := fun header member => (namedChoice header member).2
    closurePackets := fun association => (closureChoice association).1
    closureSupport := fun association => (closureChoice association).2
    owners := owners_physical rows
    methods := ?_ }⟩
  intro policy body fuel compilation source scope id reasonAt lowered context caller receipt port
  cases certificate.selection with
  | closed methods _ =>
    obtain ⟨packet, same, supported⟩ := methods.support port.principal port.sourceAt
      ⟨port.diagnostics⟩ issued wellFormed (headers := headers rows) (stages compiled)
    exact ⟨.terminal packet, same, supported⟩
  | origins methods _ =>
    exact methods.support port.principal port.sourceAt port.resolved ⟨port.diagnostics⟩ issued wellFormed
      rows aligned ready entryMember (stages compiled)

include certificate wellFormed ready issued registry entryMember rows aligned in
/-- The original public checker receipt retains its actual checking budget.
The separate static method receipt matches the compiler's method recheck. -/
theorem Certificate.issue_for_checked_with_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (methods : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) := by
  exact certificate.issue_for wellFormed ready methods
    (CallableCoercionSelectionIdentity.Catalog.of_checked accepted) issued registry entryMember rows aligned

include certificate wellFormed ready issued registry entryMember in
/-- The automatic catalog issuer also retains the actual whole-program budget. -/
theorem Certificate.issue_with_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (methods : CallableMethodBodyCoherence.Checked compiled.sourceProgram)
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) := by
  obtain ⟨catalog⟩ := CallableIndexedOwnedPreparedOrdinaryCatalog.of_compiled compiled wellFormed
  exact ⟨catalog, certificate.issue_for_checked_with_methods wellFormed ready issued registry entryMember
    catalog.rows (certificate.table.aligned catalog) methods accepted⟩

include certificate wellFormed ready issued registry entryMember rows aligned in
/-- An empty retained method catalog needs no additional body check. The actual
original checker receipt establishes that every method target is absent. -/
theorem Certificate.issue_for_without_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (empty : compiled.sourceProgram.methods = []) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) :=
  certificate.issue_for_checked_with_methods wellFormed ready issued registry entryMember rows aligned
    (CallableMethodBodyCoherence.of_empty_checked accepted empty) accepted

include certificate wellFormed ready issued registry entryMember in
theorem Certificate.issue_without_methods {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (empty : compiled.sourceProgram.methods = []) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) :=
  certificate.issue_with_methods wellFormed ready issued registry entryMember
    (CallableMethodBodyCoherence.of_empty_checked accepted empty) accepted

include certificate wellFormed ready issued registry entryMember rows aligned in
/-- Original checker success supplies the method receipt at its actual budget. -/
theorem Certificate.issue_for_checked {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    Nonempty (Support compiled (headers rows) (keys compiled) initial) :=
  certificate.issue_for_checked_with_methods wellFormed ready issued registry entryMember rows aligned
    (CallableMethodBodyCoherence.of_checked accepted) accepted

include certificate wellFormed ready issued registry entryMember in
/-- Automatic catalog construction also accepts the actual original checking budget. -/
theorem Certificate.issue {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (accepted : checkProgram raw checkingFuel = .ok compiled.sourceProgram) :
    ∃ catalog : Catalog compiled, Nonempty (Support compiled (headers catalog.rows) (keys compiled) initial) :=
  certificate.issue_with_methods wellFormed ready issued registry entryMember
    (CallableMethodBodyCoherence.of_checked accepted) accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
end
