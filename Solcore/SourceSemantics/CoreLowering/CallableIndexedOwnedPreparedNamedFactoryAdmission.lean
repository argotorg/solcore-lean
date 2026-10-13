import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors

/-! Original cached source supplies a returned-lambda formation certificate.
The inner return keeps its complete expression and coercion metadata. Actual
Header typing and accepted compilation issue the existing physical support. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedFactoryAdmission
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
  returnStatement : StatementId
  returnNode : StatementNode
  returnExpression : ExpressionId
  reported : Core.Ty
  found : source.lookupExpression? expression = some node
  form : node.form = .lambda parameters result [returnStatement]
  owner : expression.occurrence.owner = source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
      binding.initializer = expression)) = none
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
    source expression = .ok (node, reported)
  returnFound : source.lookupStatement? returnStatement = some returnNode
  returnForm : returnNode.form = .returnStmt (some returnExpression)
  returnType : returnNode.type = result

/-- Only actual lookups, metadata and the native read are evaluated. The
coerced expression inside the lambda is retained without alteration. -/
def scanSource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (body : List StatementId) : Option (SourceCertificate compiled named source body) := do
  match bodyEq : body with
  | [] => none
  | statement :: rest =>
    match statementFound : source.lookupStatement? statement with
    | none => none
    | some statementNode =>
      match statementForm : statementNode.form with
      | .returnStmt (some expression) =>
        match found : source.lookupExpression? expression with
        | none => none
        | some node =>
          match form : node.form with
          | .lambda parameters result [returnStatement] =>
            if owner : expression.occurrence.owner = source.owner then
              if requirements : node.requirements = [] then
                if coercions : node.coercions = [] then
                  if ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
                      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
                        binding.initializer = expression)) = none then
                    match read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
                        source expression with
                    | .error _ => none
                    | .ok (readNode, reported) =>
                      if same : readNode = node then
                        match returnFound : source.lookupStatement? returnStatement with
                        | none => none
                        | some returnNode =>
                          match returnForm : returnNode.form with
                          | .returnStmt (some returnExpression) =>
                            if returnType : returnNode.type = result then
                              some {
                                expression, terminal := by rw [bodyEq]; exact .returning rest statementFound statementForm,
                                node, parameters, result, returnStatement, returnNode, returnExpression,
                                reported, found, form, owner, requirements, coercions, ordinary,
                                read := by simpa only [same] using read,
                                returnFound, returnForm, returnType }
                            else none
                          | _ => none
                      else none
                  else none
                else none
              else none
            else none
          | _ => none
      | _ => none

abbrev Certificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) :=
  SourceCertificate compiled named named.specialized.function.typedBody
    (statements named.specialized.function.typedBody)

def certifyCachedFactory (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) : Option (Certificate compiled named) :=
  scanSource compiled named named.specialized.function.typedBody
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
    (same : named.specialized = row) (certificate : Certificate compiled named)
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {bodyRegistry : SourceCoreRawMetadata.Registry} {stages : Staging.Recursive.Registry}
    {semanticFaults : FunctionCalls.FaultRep} :
    ∃ terminal : Terminal header,
      Nonempty (CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
        (bodyRegistry := bodyRegistry) (stages := stages) (semanticFaults := semanticFaults) header terminal) := by
  let source := at_header prepared aligned selected same certificate
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
  exact ⟨terminal, CallableIndexedOwnedPreparedPhysicalNamedFormationCollectors.of_actual terminal
    ready diagnostic wellFormed profile member source.found source.form source.owner
    source.requirements source.coercions source.ordinary source.read source.returnFound
    source.returnForm source.returnType rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedFactoryAdmission
