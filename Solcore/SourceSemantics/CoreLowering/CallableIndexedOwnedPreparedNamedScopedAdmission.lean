import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport

/-! A finite validator admits ordinary initialized lets and value returns from
actual named source. Independent original Header typing supplies the changing
lexical contexts. The issued support uses the existing physical named family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite TableAligned)
open CallableIndexedOwnedFunctionValues (Header)

/-- Context-free admission records only actual syntax and static metadata.
The context-sensitive statement certificate is derived from original typing. -/
inductive BodyScan (source : TypedSource) (approved : ExpressionId → Prop)
    (expected : TypeSystem.Ty) : List StatementId → Prop where
  | returning {id node expression expressionNode} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression))
      (sourceType : node.type = expected)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : approved expression) : BodyScan source approved expected (id :: rest)
  | initialized {id node binder expression expressionNode rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some expression))
      (declaration : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder)
      (monomorphic : binder.scheme.quantified = [])
      (ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = binder.scheme.body)
      (value : approved expression)
      (remaining : BodyScan source approved expected rest) : BodyScan source approved expected (id :: rest)

private theorem head_tail {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context (id :: rest) final facts) :
    ∃ middle headFacts tailFacts, StatementHasType source control context id middle headFacts ∧
      StatementsHaveType source control middle rest final tailFacts := by
  cases typed with
  | singleton head => exact ⟨_, _, _, head, .nil _ _⟩
  | cons head tail => exact ⟨_, _, _, head, tail⟩

private theorem form_at {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (typed : StatementHasType source control context id final facts) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨actual, contains, original⟩ := Dynamic.StatementHasType.formTyping typed
  have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  exact original

theorem BodyScan.shape {source : TypedSource} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {statements : List StatementId}
    (scan : BodyScan source approved expected statements) :
    CallableIndexedOwnedPreparedStagedBranchingTree.Shape source true statements := by
  induction scan with
  | returning rest found form _ _ _ _ => exact .returnValue rest found form
  | initialized found form _ _ _ _ _ _ _ ih => exact .initialized found form ih

theorem BodyScan.syntax {source : TypedSource} {approved : ExpressionId → Prop}
    {expected : TypeSystem.Ty} {statements : List StatementId}
    (scan : BodyScan source approved expected statements) (unique : NodeOccurrencesUnique source)
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source {returnType := expected} context statements final facts) :
    GenericImperativeMatch.Syntax source approved context (.statements true statements) expected := by
  induction scan generalizing context final facts with
  | returning rest found form sourceType expressionFound valueType value =>
      obtain ⟨_, _, _, head, _⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | returnValue actual =>
        exact .body (.returnValue rest found form sourceType expressionFound valueType
          (by simpa only [valueType] using actual) value)
  | initialized found form declaration monomorphic ordinary expressionFound valueType value _ ih =>
      obtain ⟨_, _, _, head, tail⟩ := head_tail typed
      have original := form_at unique found head
      rw [form] at original
      cases original with
      | letInitialized actual _ extended =>
          exact .initialized found form declaration monomorphic extended ordinary expressionFound valueType
            (by simpa only [valueType] using actual) value (ih tail)
      | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly monomorphic)

/-- The finite source scanner rejects unsupported statements instead of
turning their semantics into a premise. Expression fuel only bounds scanning. -/
def scan?
    (inputs : List SourceSpecialization.SpecializedFunction) (source : TypedSource) (expected : TypeSystem.Ty) (fuel : Nat) :
    (statements : List StatementId) → Option (PLift
      (BodyScan source (fun id => GeneralSyntax source id (DirectSite inputs)) expected statements))
  | [] => none
  | id :: rest =>
      match found : source.lookupStatement? id with
      | none => none
      | some node =>
          match form : node.form with
          | .returnStmt (some expression) =>
              if sourceType : node.type = expected then
                match expressionFound : source.lookupExpression? expression with
                | none => none
                | some expressionNode =>
                    if valueType : expressionNode.type = expected then do
                      let ⟨value⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.expression? inputs source fuel expression
                      pure ⟨.returning rest found form sourceType expressionFound valueType value⟩
                    else none
              else none
          | .letDecl binder (some expression) =>
              if monomorphic : binder.scheme.quantified = [] then
                if ordinary : source.inputs.any (fun input => decide (input.id = binder.id)) = false then
                  match declared : SourceCoreDataPlaces.rootBinder source binder.id with
                  | .error _ => none
                  | .ok actual =>
                      if same : actual = binder then
                        match expressionFound : source.lookupExpression? expression with
                        | none => none
                        | some expressionNode =>
                            if valueType : expressionNode.type = binder.scheme.body then do
                              let ⟨value⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.expression? inputs source fuel expression
                              let ⟨remaining⟩ ← scan? inputs source expected fuel rest
                              pure ⟨.initialized found form (by simpa only [same] using declared)
                                monomorphic ordinary expressionFound valueType value remaining⟩
                            else none
                      else none
                else none
              else none
          | _ => none

structure SourceAdmission (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty)
    (directRows : List SourceSpecialization.SpecializedFunction) : Prop where
  metadata : CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.MetadataFor
    compiled.indexed named source (DirectSite directRows)
  body : BodyScan source (fun id => GeneralSyntax source id (DirectSite directRows)) expected statements

abbrev Admission {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (directRows : List SourceSpecialization.SpecializedFunction) : Prop :=
  SourceAdmission compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows

/-- This checker reads only compiler/source data. Neither Headers nor the
classically assembled inventory appear in the executable arguments. -/
def admitSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (statements : List StatementId) (expected : TypeSystem.Ty)
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (PLift (SourceAdmission compiled named source statements expected directRows)) := do
  let ⟨metadata⟩ ← CallableIndexedOwnedPreparedNamedSyntaxAdmission.metadata?
    compiled.indexed named source (DirectSite directRows)
  let ⟨body⟩ ← scan? directRows source expected fuel statements
  pure ⟨⟨metadata, body⟩⟩

/-- Successful certification supplies all expression syntax and native hook
metadata from the original finite tables. It does not claim every accepted
program belongs to this initial return/let fragment. -/
def admitPrepared {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (directRows : List SourceSpecialization.SpecializedFunction) (fuel : Nat) :
    Option (PLift (Admission prepared header directRows)) :=
  admitSource compiled prepared.named header.function.source header.function.body
    header.function.resultType directRows fuel

/-- Actual Header typing and accepted body compilation close the existing
scoped static issuer. Syntax, metadata, direct support and slot callbacks are
all constructed from the certification result and inventory. -/
theorem of_actual {compiled : SourceCoreUnifiedCompilation.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    {instantiation : DeclarationInstantiation}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
    {inputs : List (Input compiled)} (rows : Inventory inputs)
    {directRows : List SourceSpecialization.SpecializedFunction}
    (table : TableAligned inputs directRows)
    (admission : Admission prepared header directRows)
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {loaded : LoadedProgram}
    (checked : Frontend.checkLoadedProgram loaded 1024 = .ok compiled.sourceProgram)
    (catalog : CallableCoercionSelectionIdentity.Catalog (Program.ofChecked compiled.sourceProgram))
    (methods : CallableIndexedOwnedPreparedStagedMethodSelectionIssuer.Catalog compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {bodyRegistry : SourceCoreRawMetadata.Registry} :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry actual)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        header body) := by
  obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
  have syntaxTree := admission.body.syntax header.unique typed
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted
    aligned.accepted admission.body.shape aligned.projection
  let support := CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors.of_actual_with_catalog
    prepared aligned ready diagnostic receiver wellFormed
    (fun _ site => site.supported table) admission.metadata rows
    (fun _ site _ _ target global => site.covered rows table target global)
    checked catalog methods member receipt actual syntaxTree
  let body : CallableIndexedOwnedPreparedStagedNamedBodies.Body header := {
    row := row, prepared := prepared, instantiation := instantiation, aligned := aligned,
    layouts := aligned.layouts, compilation := .canonicalBranching receipt }
  exact ⟨body, .scoped body receipt rfl support⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedScopedAdmission
