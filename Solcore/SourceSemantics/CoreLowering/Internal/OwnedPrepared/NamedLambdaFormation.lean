import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.Bootstrap
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ContextualOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.PreparedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NativeCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LambdaReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.AcceptedPackets
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.OrdinaryLambdas
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LiteralReturns
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.BodyReadyState
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.CatalogTerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.ProfileExtraction

/-!
# Prepared callables: named lambda formation

Lexical and same-policy lambda producers and formation of named bodies, and evidence admission.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedFactoryAdmission
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaProducer
/-! The real named expression callback retains an ordinary lambda at any
actual lexical scope. Native child typing comes from the enclosing accepted
body, and its literal callable constructors determine the result type. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {childFuel : Nat}
  {lowered : SourceCoreBasic.LoweredExpr}

include aligned in
/-- Original Source and output equalities belong to the same chosen Site.
The complete compiler policy is retained before any later recapture. -/
theorem of_expression
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {node : ExpressionNode} {reported : Ty}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : id.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧
        binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source id = .ok (node, reported))
    (accepted : header.policy.lowerExpression childFuel header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    ∃ produced : Produced (compiled := compiled) header.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt := by
  have expressionPolicy : header.policy.lowerExpression =
      (RecursiveNamedPreparedHeaders.Prepared.policy prepared).lowerExpression :=
    congrArg SourceCoreLoops.Policy.lowerExpression aligned.policy
  rw [expressionPolicy] at accepted
  change SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext prepared.named.signature.key [])
    compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.locals
    prepared.compilation.parents prepared.compilation.own.assignments prepared.diagnostics
    (context compiled.indexed prepared.named) compiled.indexed.base.callableContext none none
    childFuel header.function.source
    scope id header.reasonAt =
      .ok lowered at accepted
  have nonzero : childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have sourceEq : header.function.source = source prepared.named :=
    header.agreement.source.trans (congrArg source aligned.named)
  have record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan
      prepared.named.signature.key = .ok prepared.named.specialized := by
    simpa only [aligned.named] using CallableIndexedActualNamedSourceReceipts.header_record compiled header
  have actualAccepted := fuelEq ▸ accepted
  obtain ⟨policy, lowerBody, _accepted, ⟨certificate⟩, _allocationProfile, _manifest,
      expressionProfile, callables, _projector, _binderPolicy, _bodyRecipe, _policyRecipe⟩ :=
    CallableIndexedLambdaGeneration.contextual_certificate_with_policy_recipe compiled.indexed
      prepared.compilation record found form owner requirements coercions ordinary read actualAccepted
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate found expressionProfile callables nativeTyped
  obtain ⟨site, identifier, emitted, binderPolicy, _bodyRecipe, issuedRecipe, view, reasonAt⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact compiled.indexed
      prepared.compilation (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic) record sourceContext evidence [] profile
      (by rw [← sourceEq]; exact LambdaMetadataViews.MetadataView.refl _)
      (by simpa only [← sourceEq] using found) form found rfl owner requirements coercions ordinary read
      (by simpa only [fuelEq] using accepted) native
  let rawProduced : Produced (compiled := compiled) prepared.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := binderPolicy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
  have actual : ∃ produced : Produced (compiled := compiled) prepared.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt :=
    ⟨rawProduced, view, reasonAt⟩
  let Property (named : Named) : Prop :=
    ∃ produced : Produced (compiled := compiled) named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt
  exact Eq.mp (congrArg Property aligned.named.symm) actual

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaFormation
/-! The same original lambda producer works after real lexical bindings.
Only static context transport, original Source typing, and native typing of
the actual compiler child are used; captures remain runtime inputs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {childFuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

include aligned in
/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_expression
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : id.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧
        binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source id = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result)
    (fields : Dynamic.RuntimeContextFields header.context sourceContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext)
    (sourceTyped : ExpressionHasType header.function.source sourceContext id node.type)
    (accepted : header.policy.lowerExpression childFuel header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header sourceContext child.evidence
      scope
      id lowered) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLexicalLambdaProducer.of_expression
    (sourceContext := sourceContext) (evidence := child.evidence) prepared aligned profile diagnostic
    found form owner requirements coercions ordinary read accepted nativeTyped
  have actualFound : header.function.source.lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  have sourceTyped : ExpressionHasType header.function.source sourceContext id produced.site.code.sourceNode.type :=
    sameNode.symm ▸ sourceTyped
  let function := closure header.named parameters result [statement] sourceContext child.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport ((RecursiveNamedInitialContextValidity.mono_fields header.extended).trans fields)
  have covers : function.evidence.Covers function.context := by
    change child.evidence.Covers sourceContext
    rw [stages.evidence selected]
    exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended)
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      scope.length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact fields.solvedRequirements.trans (header.valid.ledger.trans (aligned.solved.trans (by rw [aligned.named]; rfl)))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have invocationSource : child.source = function.source :=
    (stages.source selected).trans original.symm
  have returnFound : function.source.lookupStatement? statement = some returnNode := by
    simpa only [original] using returnFound
  have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression function.body := by
    change CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression [statement]
    exact .returning [] (by rw [invocationSource]; exact lookupStatement?_sound returnFound) returnForm
  obtain ⟨readNode, childFound, childType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters frame inputs.extended invocationSource head
  rw [invocationSource] at childFound childTyped
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  obtain ⟨lowered, body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedReturnLambdaBodySupport.of_return
    produced.site.code produced.recipe inputs frame ledger profile actualView rfl
    returnFound returnForm returnType childFound childType childTyped
  rw [header.agreement.source] at declarations
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Syntax expression)
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Child expression lowered) body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared prepared diagnostic aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header prepared aligned fields
      ((stages.evidence selected).trans (congrArg (fun function => function.evidence) aligned.function)))⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer
/-! An ordinary lambda below a recursive expression retains the original root
policy at its actual child fuel. Native child typing determines the emitted
callable type, and the retained producer keeps that exact Site and policy. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaProducerReceipts (Produced)
open CallableIndexedOwnedContextualCompilerPolicyProfiles

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics prepared.code
    prepared.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {childFuel : Nat}
  {lowered : SourceCoreBasic.LoweredExpr}

include aligned in
/-- Original Source and output equalities belong to the same chosen Site.
The complete compiler policy is retained before any later recapture. -/
theorem of_expression
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {node : ExpressionNode} {reported : Ty}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : id.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧
        binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source id = .ok (node, reported))
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      childFuel (context compiled.indexed prepared.named) header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    ∃ produced : Produced (compiled := compiled) header.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt := by
  have nonzero : childFuel ≠ 0 := by
    intro zero
    simp only [zero, SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    cases accepted
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  have sourceEq : header.function.source = source prepared.named :=
    header.agreement.source.trans (congrArg source aligned.named)
  have actualAccepted := fuelEq ▸ accepted
  have pointwise := lambda_policy root (scope := scope) (reasonAt := header.reasonAt)
    found form requirements coercions ordinary
  have special : DecoratedFunctionCode.SpecialPasses root.selected.policy root.selected.lowerBody fuel
      (context compiled.indexed prepared.named) header.function.source scope id header.reasonAt :=
    pointwise.special _ _
  obtain ⟨certificate⟩ := CallableIndexedLambdaCertificates.of_accepted special owner found
    (pointwise.read.trans read) form actualAccepted
  have native := CallableIndexedOwnedPreparedLambdaOccurrenceNativeTyping.certificate_native
    compiled.indexed certificate found root.rawLambdaExpression root.callables nativeTyped
  obtain ⟨site, identifier, emitted, samePolicy, sameBody, _sameFuel, view, reasonAt,
      _sourceNode, _node, _sameCertificate⟩ :=
    CallableIndexedLambdaGeneration.of_certificate compiled.indexed sourceContext evidence [] certificate actualAccepted
      profile (by rw [← sourceEq]; exact LambdaMetadataViews.MetadataView.refl _)
      (by simpa only [← sourceEq] using found) form found rfl
      root.sourceCells root.rawLambdaBody root.rawLambdaExpression root.callables root.projectType
      (by rw [root.compilerPolicy.snapshotLambda]) native
  have issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained prepared.named site.code := by
    apply CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained.of_recipes (rootFuel := rootFuel)
      prepared.compilation (CallableIndexedOwnedIssuedAssignmentRecipes.of_prepared prepared diagnostic) (sameBody.trans root.selected.recipe) _ site.compilation
    rw [samePolicy]
    exact root.compilerPolicy
  have binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy prepared.named site.code :=
    (congrArg SourceCoreFunctions.Policy.lowerBinder samePolicy).trans root.selected.binder
  let rawProduced : Produced (compiled := compiled) prepared.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered := {
    site := site
    identifier := identifier
    emitted := emitted
    binderPolicy := binderPolicy
    recipe := issuedRecipe.body_recipe
    compilerPolicy := issuedRecipe.policy_recipe
    issuedRecipe := issuedRecipe }
  have actual : ∃ produced : Produced (compiled := compiled) prepared.named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt :=
    ⟨rawProduced, view, reasonAt⟩
  let Property (named : Named) : Prop :=
    ∃ produced : Produced (compiled := compiled) named parameters result statements sourceContext evidence
      scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      id lowered,
      produced.site.code.view = header.function.source ∧ produced.site.code.reasonAt = header.reasonAt
  exact Eq.mp (congrArg Property aligned.named.symm) actual

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaFormation
/-! An actual lambda child below a recursive expression uses its retained root
policy and reached lexical context. Original Source typing and native child
typing construct the same formation receipt; captures come from execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedContextualCompilerPolicyProfiles
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) prepared.named prepared.diagnostics prepared.code
    prepared.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {childFuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

include aligned in
/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_expression
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statement : StatementId} {returnNode : StatementNode} {expression : ExpressionId}
    (found : header.function.source.lookupExpression? id = some node)
    (form : node.form = .lambda parameters result [statement])
    (owner : id.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed prepared.named).owner ∧
        binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source id = .ok (node, reported))
    (returnFound : header.function.source.lookupStatement? statement = some returnNode)
    (returnForm : returnNode.form = .returnStmt (some expression))
    (returnType : returnNode.type = result)
    (fields : Dynamic.RuntimeContextFields header.context sourceContext)
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source scope sourceContext)
    (sourceTyped : ExpressionHasType header.function.source sourceContext id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      childFuel (context compiled.indexed prepared.named) header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header sourceContext child.evidence
      scope
      id lowered) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedSamePolicyLambdaProducer.of_expression
    (sourceContext := sourceContext) (evidence := child.evidence) prepared aligned root profile diagnostic
    found form owner requirements coercions ordinary read accepted nativeTyped
  have actualFound : header.function.source.lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  have sourceTyped : ExpressionHasType header.function.source sourceContext id produced.site.code.sourceNode.type :=
    sameNode.symm ▸ sourceTyped
  let function := closure header.named parameters result [statement] sourceContext child.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function id produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport ((RecursiveNamedInitialContextValidity.mono_fields header.extended).trans fields)
  have covers : function.evidence.Covers function.context := by
    change child.evidence.Covers sourceContext
    rw [stages.evidence selected]
    exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended)
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      scope.length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, _bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact fields.solvedRequirements.trans (header.valid.ledger.trans (aligned.solved.trans (by rw [aligned.named]; rfl)))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have invocationSource : child.source = function.source :=
    (stages.source selected).trans original.symm
  have returnFound : function.source.lookupStatement? statement = some returnNode := by
    simpa only [original] using returnFound
  have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression function.body := by
    change CallableIndexedOwnedAdmittedStagedTerminalStatements.Head child expression [statement]
    exact .returning [] (by rw [invocationSource]; exact lookupStatement?_sound returnFound) returnForm
  obtain ⟨readNode, childFound, childType, childTyped⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.at_parameters frame inputs.extended invocationSource head
  rw [invocationSource] at childFound childTyped
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  obtain ⟨lowered, body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedReturnLambdaBodySupport.of_return
    produced.site.code produced.recipe inputs frame ledger profile actualView rfl
    returnFound returnForm returnType childFound childType childTyped
  rw [header.agreement.source] at declarations
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Syntax expression)
    (CallableIndexedOwnedPreparedReturnLambdaBodySupport.Child expression lowered) body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared prepared diagnostic aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header prepared aligned fields
      ((stages.evidence selected).trans (congrArg (fun function => function.evidence) aligned.function)))⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSamePolicyLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
/-! Original named compiler children can combine general calls with closure
formation after lexical allocation. Both alternatives retain the accepted
callback, original typing and actual context; runtime captures come from entry. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- Finite observations identify the original ordinary lambda occurrence and
its single return statement. The returned expression is checked separately by
the same retained closure family when the resulting handle is invoked. -/
structure ReturnLambda (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (id : ExpressionId) where
  node : ExpressionNode
  reported : Ty
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statement : StatementId
  returnNode : StatementNode
  expression : ExpressionId
  found : header.function.source.lookupExpression? id = some node
  form : node.form = .lambda parameters result [statement]
  owner : id.occurrence.owner = header.function.source.owner
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed header.named).owner ∧
      binding.initializer = id)) = none
  read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
    header.function.source id = .ok (node, reported)
  returnFound : header.function.source.lookupStatement? statement = some returnNode
  returnForm : returnNode.form = .returnStmt (some expression)
  returnType : returnNode.type = result

/-- Container observations are original node facts. The actual root policy
remains selected once while its recursive children use their smaller budgets. -/
structure Container (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    (id : ExpressionId) where
  node : ExpressionNode
  found : header.function.source.lookupExpression? id = some node
  requirements : node.requirements = []
  coercions : node.coercions = []
  ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed header.named).owner ∧
      binding.initializer = id)) = none

inductive Syntax (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : ExpressionId → Prop where
  | general {id} (tree : GeneralSyntax header.function.source id) : Syntax header id
  | formation {id} (shape : ReturnLambda header id) : Syntax header id
  | group {id inner} (shape : Container header id) (form : shape.node.form = .group inner)
      (child : Syntax header inner) : Syntax header id
  | tuple {id ids} (shape : Container header id) (form : shape.node.form = .tuple ids)
      (children : ∀ child, child ∈ ids → Syntax header child) : Syntax header id

private theorem container_policy
    {named : CallableIndexedNamedGeneration.Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      named diagnostics namedCode compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : (∃ inner, node.form = .group inner) ∨ ∃ ids, node.form = .tuple ids)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (CallableIndexedNamedGeneration.context compiled.indexed named).owner ∧
        binding.initializer = id)) = none) :
    CallableIndexedOwnedContextualCompilerPolicyProfiles.PointwiseFor root source scope id reasonAt := by
  rcases form with ⟨inner, form⟩ | ⟨ids, form⟩
  all_goals
    have sameSource : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
        (CallableIndexedNamedGeneration.context compiled.indexed named).plan compiled.indexed.base.locals
        (CallableIndexedNamedGeneration.context compiled.indexed named).owner none source id = .ok source := by
      simp [SourceCoreGeneralFunctions.contextualSource, found, form]
    constructor
    · rw [root.selected.readExpression]
      simp only [sameSource, bind, Except.bind]
      rw [CallableIndexedOwnedIndirectCompilerPolicyInputs.representation_read]
    · intro child budget
      rw [root.selected.special_eq, root.selected.special_body]
      have owned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some [] := by
        unfold SourceCompilationPlan.ordinaryOwnedRequirements?
        rw [requirements, coercions]
        rfl
      have noEvidence : SourceCoreEvidence.lowerWithProjector compiled.indexed.base.sourceProgram
          ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key []).expressions.projectType
          named.specialized (CallableIndexedNamedGeneration.context compiled.indexed named)
          child budget source scope id reasonAt
          (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext []) = .ok none := by
        simp [SourceCoreEvidence.lowerWithProjector, found, form, owned, requirements, coercions]
      simp only [sameSource, bind, Except.bind, found, pure, Except.pure, ordinary,
        Option.filter_none, noEvidence, form]

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem child_certificates
    {source : TypedSource} {context : SourceSemantics.Context}
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {budget : Nat}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    {nativeContext : Core.Context} {definitions : DataEnvironment}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body budget
      compilation source scope id reasonAt) = .ok codes)
    (native : ∀ code, code ∈ codes → ∃ type, HasType nativeContext code.expression type definitions)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code →
      (∃ type, HasType nativeContext code.expression type definitions) → certificate id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      ∀ id code, (id, code) ∈ ids.zip codes → certificate id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first (native code (by simp))
      obtain ⟨count, nodes, children⟩ := ih tail rest
        (fun child member => native child (by simp [member]))
        (fun child member => extract child (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_⟩
      intro other otherCode member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact child
      · exact children other otherCode remaining

variable {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)


include aligned in
private theorem of_policy
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed prepared.named header.function.source)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    {child : Staging.Recursive.Scope}
    (selected : (RecursiveNamedPreparedStageScopes.registry actual).Closure header.function child)
    {context : SourceSemantics.Context}
    (fields : Dynamic.RuntimeContextFields header.context context)
    {scope : SourceCoreLocalCell.Scope}
    (declarations : CompatibleExpressionReads.ScopeDeclarations header.function.source scope context)
    {id : ExpressionId} (approved : Syntax header id)
    {node : ExpressionNode}
    (found : header.function.source.lookupExpression? id = some node)
    (typed : ExpressionHasType header.function.source context id node.type)
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt (compiled := compiled)
      prepared.named prepared.diagnostics prepared.code prepared.compilation rootFuel
      rootSource rootScope rootId rootReasonAt rootLowered)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody fuel
      (CallableIndexedNamedGeneration.context compiled.indexed prepared.named)
      header.function.source scope id header.reasonAt = .ok lowered)
    {nativeType : Ty}
    (native : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) header)
      lowered.expression nativeType compiled.indexed.layouts.definitions) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.Certificate
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) header bodyRegistry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      context child scope id lowered := by
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context child.source := by
    rw [sameSource]
    exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)).transport fields
  have covers : child.evidence.Covers context := by
    rw [(RecursiveNamedPreparedStageScopes.registry actual).evidence selected]
    exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended)
  induction approved generalizing node fuel lowered nativeType with
  | general tree =>
    obtain ⟨actualRoot, samePrefix⟩ := CallableIndexedOwnedPreparedStagedNamedCanonicalScopedRoots.of_policy
      prepared aligned diagnostic receiver wellFormed metadata rows complete actual selected fields
      (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using tree)
      (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed) root
      (by simpa only [sameSource] using accepted)
    exact .canonical actualRoot samePrefix
  | formation shape =>
    have sameNode : node = shape.node := Option.some.inj (found.symm.trans shape.found)
    subst node
    obtain ⟨formation⟩ := CallableIndexedOwnedPreparedNamedSamePolicyLambdaFormation.of_expression
      prepared aligned root diagnostic wellFormed profile selected found shape.form shape.owner
      shape.requirements shape.coercions
      (by simpa only [aligned.named] using shape.ordinary) shape.read
      shape.returnFound shape.returnForm shape.returnType fields declarations typed accepted native
    exact .legacy (.formation formation runtime covers)
  | group shape form _child ih =>
    have sameNode : node = shape.node := Option.some.inj (found.symm.trans shape.found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have pointwise := container_policy root (scope := scope) (reasonAt := header.reasonAt)
        found (.inl ⟨_, form⟩) shape.requirements shape.coercions
        (by simpa only [aligned.named] using shape.ordinary)
      have step := CompatibleExpressionConditionals.step_of_functions (values := .initial compiled.compatible.checked) found (by rw [form]; constructor)
        pointwise.special pointwise.read accepted
      cases step with
      | group otherForm actualMetadata generated =>
        cases ExpressionForm.group.inj (form.symm.trans otherForm)
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types header.unique found form actualMetadata.coercions typed
        exact .group (by simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using actualMetadata) form
          (by simpa only [sameSource] using innerFound) sourceType
          (ih innerFound childTyped generated native)
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ =>
        simp [form] at otherForm
  | tuple shape form children ih =>
    have sameNode : node = shape.node := Option.some.inj (found.symm.trans shape.found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have pointwise := container_policy root (scope := scope) (reasonAt := header.reasonAt)
        found (.inr ⟨_, form⟩) shape.requirements shape.coercions
        (by simpa only [aligned.named] using shape.ordinary)
      obtain ⟨codes, generated, rfl, actualMetadata⟩ := CompatibleExpressionTuples.of_functions
        found form pointwise.special pointwise.read root.compilerPolicy.leafLowerer accepted
      obtain ⟨types, childTyped, sourceType⟩ := CompatibleExpressionTuples.source_types
        header.unique found form actualMetadata.coercions typed
      obtain ⟨count, nodes, certified⟩ := child_certificates header.unique childTyped generated
        (CallableIndexedOwnedPreparedNativeAssignmentChildren.packed_children native)
        (fun child member childNode code childFound childTyped childAccepted childNative => by
          obtain ⟨type, typed⟩ := childNative
          exact ih child member childFound childTyped childAccepted typed)
      refine .tuple runtime covers ⟨?_, form, sourceType⟩
        (CompatibleExpressionConstructors.sequence_of_nodes count
          (by simpa only [sameSource] using nodes)
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified
      simpa only [sameSource, SourceCoreCompatibleValues.Context.initial] using actualMetadata

include aligned in
/-- The complete inventory and original compiler observations construct both
canonical call children and ordinary formation at every actual lexical scope. -/
def of_actual
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      compiled.indexed prepared.named header.function.source)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.Syntax header.function.source (Syntax header)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors.of_imperative_compiler
    prepared aligned ready diagnostic wellFormed complete zero member receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic prepared aligned diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic prepared aligned diagnostic receiver)
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree.prepared
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  obtain ⟨predecessor, ⟨root⟩⟩ := CallableIndexedOwnedPreparedStagedNamedLexicalReadRoots.policy_receipt
    prepared aligned accepted
  exact of_policy prepared aligned diagnostic receiver wellFormed profile metadata rows complete actual selected
    fields declarations approved found typed root root.selected.accepted native

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors
/-! Actual scoped compiler trees issue evidence-aware expression support.
Local initialization, assignment and control flow retain the full caller
ledger and dictionary through the existing shared body proof. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt parameterScope)
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

include aligned in
/-- The actual prepared Header, complete inventory and native metadata issue
all canonical children without exposing a child execution premise. -/
def of_actual
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {directSites : DeclarationInstantiation → Prop}
    (supported : ∀ instantiation, directSites instantiation →
      CallableIndexedOwnedPreparedStagedDirectCallCertificates.Supported compiled.indexed.base.plan instantiation)
    (metadata : CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source directSites)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (receipt : Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source (fun id => GeneralSyntax header.function.source id directSites)
      header.context (.statements true header.function.body) header.function.resultType) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows) keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry actual) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors.of_imperative_compiler prepared aligned ready diagnostic wellFormed complete zero member receipt
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.operands_of_diagnostic prepared aligned diagnostic receiver)
    (CallableIndexedOwnedPreparedNamedBranchingCollectors.unary_of_diagnostic prepared aligned diagnostic receiver)
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  obtain ⟨root, prefixEq⟩ := CallableIndexedOwnedPreparedStagedNamedEvidenceScopedRoots.of_accepted_sites
    prepared aligned diagnostic receiver wellFormed supported metadata rows complete actual selected fields
    (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using approved)
    (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed)
    (by simpa only [sameSource] using accepted)
  exact .canonical root prefixEq

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceAdmission
/-! The same data-only syntax admission feeds existing evidence-aware scoped
bodies. A finite requirements check preserves the stronger metadata profile
needed by that family, including grammar-supported nodes outside the body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceAdmission
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedNamedSourceAdmissionTransport
open CallableIndexedOwnedPreparedNamedScopedAdmission (SourceAdmission Admission)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)

def OrdinaryRequirements (node : ExpressionNode) : Prop :=
  match node.form with
  | .integerLiteral _ _ => True
  | .call _ _ (.declaration _) => True
  | _ => node.requirements = []

instance (node : ExpressionNode) : Decidable (OrdinaryRequirements node) := by
  unfold OrdinaryRequirements
  split <;> infer_instance

private theorem ordinary_requirements {node : ExpressionNode} (checked : OrdinaryRequirements node) :
    node.requirements = [] ∨ (∃ literal resolution, node.form = .integerLiteral literal resolution) ∨
      ∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation) := by
  unfold OrdinaryRequirements at checked
  split at checked
  · exact .inr (.inl ⟨_, _, by assumption⟩)
  · exact .inr (.inr ⟨_, _, _, by assumption⟩)
  · exact .inl checked

def Requirements (source : TypedSource) : Prop :=
  ∀ id node, source.lookupExpression? id = some node →
    node.requirements = [] ∨ (∃ literal resolution, node.form = .integerLiteral literal resolution) ∨
      ∃ callee ids instantiation, node.form = .call callee ids (.declaration instantiation)

/-- This check covers every actual expression in the original finite table.
Unused operator nodes cannot silently acquire a weaker metadata restriction. -/
def requirements? (source : TypedSource) : Option (PLift (Requirements source)) :=
  if checked : source.nodes.all (fun node => match node with
      | .expression expression => decide (OrdinaryRequirements expression)
      | .statement _ => true) = true then
    some ⟨by
      intro id node found
      have member := (lookupExpression?_sound found).1
      have selected := List.all_eq_true.mp checked (.expression node) member
      exact ordinary_requirements (by simpa only [decide_eq_true_eq] using selected)⟩
  else none

structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled)
    (named : SourceCoreGeneralFunctions.Function) where
  table : CallableIndexedOwnedPreparedOrdinarySyntaxTable.Table compiled
  sourceAdmission : SourceAdmission compiled named named.specialized.function.typedBody
    (statements named.specialized.function.typedBody) named.specialized.function.inferredBodyType table.rows
  requirements : Requirements named.specialized.function.typedBody

/-- No semantic catalog or classically selected Header is an executable input.
The cache table, original syntax and evidence restriction are certified together. -/
def certifySource (compiled : SourceCoreUnifiedCompilation.Compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (named : SourceCoreGeneralFunctions.Function) (fuel : Nat) :
    Option (Certificate compiled named) := do
  let checked ← CallableIndexedOwnedPreparedNamedCatalogAdmission.certifySource compiled wellFormed
    named named.specialized.function.typedBody (statements named.specialized.function.typedBody)
    named.specialized.function.inferredBodyType fuel
  let ⟨requirements⟩ ← requirements? named.specialized.function.typedBody
  pure ⟨checked.table, checked.sourceAdmission, requirements⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {index : Nat} {named : SourceCoreGeneralFunctions.Function}
  (selected : compiled.indexed.base.functions[index]? = some named)
  (same : named.specialized = row)
  (certificate : Certificate compiled named)

include prepared aligned selected same certificate in
theorem at_header : Admission prepared header certificate.table.rows :=
  source_at_header prepared aligned selected same certificate.sourceAdmission

include prepared aligned selected same certificate in
theorem metadata_at_header :
    CallableIndexedOwnedPreparedStagedGeneralCallerEvidenceProfiles.MetadataFor
      compiled.indexed prepared.named header.function.source (DirectSite certificate.table.rows) := by
  have admission := at_header prepared aligned selected same certificate
  refine ⟨?_, admission.metadata.coercions, admission.metadata.initializer,
    admission.metadata.arguments, admission.metadata.localRead⟩
  intro id _tree node found
  rw [(header_data prepared aligned).1, cached_named prepared selected same] at found
  exact certificate.requirements id node found

include prepared aligned selected same certificate in
/-- Actual accepted statement compilation supplies the receipt; the source
checker supplies only its static shape. -/
theorem receipt : Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header) :=
  CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted aligned.accepted
    (at_header prepared aligned selected same certificate).body.shape aligned.projection

/-- Existing complete ordinary inventories cover the actual scanned cache;
all direct support, metadata and statement syntax are constructed internally. -/
def of_receipt {inputs : List (Input compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers rows))
    {recipe : SourceCoreIndexedSession.Recipe}
    (ready : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    (zero : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys, owner.key.capturePrefix = 0)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    (bodyReceipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt header)
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled compiled.indexed.ancestry.graph.inputs.callable) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (headers rows) keys bodyRegistry header (RecursiveNamedPreparedStageScopes.registry actual)
      bodyReceipt (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  have admission := at_header prepared aligned selected same certificate
  have table := table_aligned_of_complete rows complete certificate.table
  have syntaxTree : GenericImperativeMatch.PreparedSyntax header.function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        header.function.source id (DirectSite certificate.table.rows))
      header.context (.statements true header.function.body) header.function.resultType := by
    obtain ⟨final, facts, typed, _complete⟩ := RecursiveNamedHeaderSourceTyping.statements header wellFormed
    exact admission.body.syntax header.unique typed
  exact CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors.of_actual prepared aligned
    ready diagnostic receiver wellFormed (fun _ site => site.supported table)
    (metadata_at_header prepared aligned selected same certificate) rows complete zero member
    bodyReceipt actual syntaxTree

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalBodyLambdaFormation
/-! Actual named compilation retains the same lambda and its complete
lexical body. Original checked Source typing supplies the captured context;
no child execution law or body certificate is supplied by callers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalBodyLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaFormationReceipts (OrdinaryFormation)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (terminal : Terminal header)
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Finite shape observations are at the original successfully lowered nodes. -/
theorem of_terminal
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (diagnostic : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt terminal.prepared)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {stages : Staging.Recursive.Registry} {child : Staging.Recursive.Scope}
    (selected : stages.Closure header.function child)
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
    (member : entry ∈ compiled.indexed.entries)
    {node : ExpressionNode} {reported : Ty} {result : TypeSystem.Ty}
    {parameters : List TypedBinder}
    {statements : List StatementId}
    (found : header.function.source.lookupExpression? terminal.expression = some node)
    (form : node.form = .lambda parameters result statements)
    (owner : terminal.expression.occurrence.owner = header.function.source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed terminal.prepared.named).owner ∧
        binding.initializer = terminal.expression)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked
      header.function.source terminal.expression = .ok (node, reported))
    (syntaxFor : ∀ {context final bodyFacts},
      StatementsHaveType header.function.source {returnType := result} context statements final bodyFacts →
      GenericLexicalStatements.Syntax header.function.source
        (CallableIndexedOwnedPreparedLexicalLambdaBodySupport.Syntax header.function.source)
        context true statements result) :
    Nonempty (OrdinaryFormation (registry := registry) (faults := faults)
      header header.context header.function.evidence
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      terminal.expression terminal.receipt.child) := by
  obtain ⟨produced, view, reason⟩ := CallableIndexedOwnedPreparedNamedLambdaProducer.of_terminal terminal
    prepared profile diagnostic member found form owner requirements coercions ordinary read
  have actualFound : header.function.source.lookupExpression? terminal.expression = some produced.site.code.sourceNode := by
    simpa only [closure, produced.identifier, source, ← header.agreement.source] using produced.site.code.sourceFound
  have sameNode : produced.site.code.sourceNode = node := Option.some.inj (actualFound.symm.trans found)
  obtain ⟨typedNode, typedFound, _, sourceTyped⟩ :=
    CallableIndexedOwnedPreparedStagedNamedTerminalChildReceipts.source_child terminal.receipt selected wellFormed
  have typedSame : typedNode = produced.site.code.sourceNode := Option.some.inj (typedFound.symm.trans actualFound)
  cases typedSame
  let function := closure header.named parameters result statements header.context header.function.evidence []
  have facts : CallableIndexedOwnedOrdinaryLambdaSourceFacts.Facts function terminal.expression produced.site.code.sourceNode :=
    CallableIndexedOwnedOrdinaryLambdaSourceFacts.of_typed
      (by simpa only [function, closure, source, header.agreement.source] using header.unique)
      (by simpa only [function, closure, source, header.agreement.source] using actualFound)
      produced.site.code.sourceForm
      (by simpa only [function, closure, source, header.agreement.source] using sourceTyped)
      (sameNode ▸ coercions)
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  have sourceRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
    rw [header.frame.context, header.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source := by
    simpa only [function, closure, source, header.agreement.source] using
      sourceRuntime.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)
  have covers : function.evidence.Covers function.context := by
    change header.function.evidence.Covers header.context
    exact RecursiveNamedInitialContextValidity.covers header.frame header.extended
  have frame := facts.frame runtime covers
  have ownership : LocalIdentityOwnership function.source := by
    change LocalIdentityOwnership (source header.named)
    change LocalIdentityOwnership header.named.specialized.function.typedBody
    rw [← header.agreement.source, header.frame.source]
    exact certificate.local_identity_ownership
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) produced.site.code ownership facts.contains facts.form
  have referenceIndex : produced.site.code.referenceIndex =
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 +
        compiled.indexed.base.globals.length := by
    change SourceCoreCallableIndexedAncestry.creationReferenceIndex produced.site.code.compilation _ = _
    rw [produced.site.compilation]
    rfl
  obtain ⟨inputs, _finalContext, _bodyFacts, bodyTyped, _completes⟩ :=
    CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_of_source_facts
      (values := .initial compiled.compatible.checked) produced.site.code facts kinds referenceIndex
  have ledger : function.context.solvedRequirements = produced.site.code.compilation.solvedRequirements := by
    rw [produced.site.compilation]
    exact header.valid.ledger.trans (terminal.aligned.solved.trans (by rw [terminal.aligned.named]; rfl))
  have original : function.source = header.function.source := by
    simpa only [function, closure, source] using header.agreement.source.symm
  have actualView : produced.site.code.view = function.source := view.trans original.symm
  have declarations := RecursiveNamedHeaderScopeDeclarations.header_scope
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (prepared := compiled.indexed.ancestry) (program := Program.ofChecked compiled.sourceProgram) header
  rw [header.agreement.source] at declarations
  have entryDeclarations := CallableIndexedOwnedLiteralReturnLambdaStaticFacts.entry_declarations
    (values := .initial compiled.compatible.checked) produced.site.code inputs facts declarations
  have signatures : inputs.context.signatures = compiled.compatible.checked.signatures := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).signatures.trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := header))
  have syntaxTree : GenericLexicalStatements.Syntax function.source
      (CallableIndexedOwnedPreparedLexicalLambdaBodySupport.Syntax function.source)
      inputs.context true function.body function.resultType := by
    have typed : StatementsHaveType header.function.source {returnType := result}
        inputs.context statements _finalContext _bodyFacts := by
      simpa only [function, closure, source, ← header.agreement.source] using bodyTyped
    simpa only [function, closure, source, ← header.agreement.source] using syntaxFor typed
  obtain ⟨body, _sameInputs, syntaxTree⟩ := CallableIndexedOwnedPreparedLexicalLambdaBodySupport.of_lexical
    produced.site.code produced.recipe inputs frame ledger profile actualView
    (by rw [produced.site.compilation]; rfl) produced.site.active produced.site.allocationError
    signatures entryDeclarations syntaxTree
  exact ⟨CallableIndexedOwnedContextualLambdaFormationReceipts.ordinary_of_producer header produced
    CallableIndexedOwnedPreparedLexicalLambdaBodySupport.Syntax
    CallableIndexedOwnedPreparedLexicalLambdaBodySupport.Child body
    (by intro id _reached; rw [actualView])
    (CallableIndexedOwnedContextualLambdaReadDiagnostics.of_prepared terminal.prepared diagnostic terminal.aligned reason)
    declarations
    syntaxTree facts.sourceType facts.ordinary facts.coercions
    (CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt.of_header terminal.prepared terminal.aligned
      (.refl _) (congrArg (fun function => function.evidence) terminal.aligned.function))⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalBodyLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedProfileFamilies
/-! A selected finite row and positive bootstrap owner construct the named
profile family at actual parameter entries. Each request runs the enclosing
native collector on that entry and retains its original diagnostic issuer.
The continuations consume the resulting family internally. Strict body flow
remains an induction hypothesis; no static input contains a body execution law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedProfileFamilies
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Header)
open CallableIndexedOwnedPreparedCatalogNamedBodyContinuations (Profile FlowPreserves FlowReflects)
open CallableIndexedOwnedNamedBootstrapReceipts (NamedOwner)
open RecursiveNamedCatalogInvocationBounds (Below)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {input : Input compiled}
  (packet : Issued input)
  {headers : List (Header compiled)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : Header compiled → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled → ExpressionId → Prop}
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {nativeEntry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts}
  (nativeMember : nativeEntry ∈ compiled.indexed.entries)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (origin : NamedOwner (headers := headers) keys functions registry)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (children : ∀ administrative, CallableIndexedOwnedPreparedDirectNamedProfileExtraction.Children
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (header := packet.header) (administrative := administrative))

include accepted nativeMember complete wellFormed children in
/-- Construct the same rich profile from the real parameter entry. The zero
capture prefix is proved by the retained bootstrap token and key embedding. -/
theorem profiles :
    Nonempty (CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.ProfilesFor
      (headers := headers) (registry := registry) (certificates := certificates) (expressionSyntax := expressionSyntax)
      functions origin.owner (header := packet.header)) := by
  refine ⟨?_⟩
  intro arguments before initialStore mapping world administrative actualContext actual ξ frameLocation current ghost entry
  have captureZero := origin.capture_zero
  rw [captureZero] at entry
  exact Classical.choice (CallableIndexedOwnedPreparedFiniteCatalogNamedProfiles.extract_at
    packet accepted nativeMember functions origin.owner complete entry wellFormed (children administrative))

variable (member : packet.header ∈ headers)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (caller : CallableIndexedOwnedFunctionState.State headers keys
    ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value}
  (beforeTyped : Dynamic.HeapWellTyped packet.header.function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes packet.header.function.context before arguments packet.header.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

include accepted nativeMember complete wellFormed children member beforeTyped argumentsTyped stable in
/-- Source continuation has no externally supplied profile family, capture
equality, global size, or Source body syntax. The actual collector supplies the
family and its local static children supply the syntax. -/
theorem source_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) packet.header administrative),
      FlowPreserves (registry := registry) (faults := faults) (headers := headers)
        functions origin.owner profile child)) :
    CallableIndexedOwnedInvocationBounds.SourceContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := packet.header) (arguments := arguments) origin.owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := origin.owner.key.locations) (capturePrefix := origin.owner.key.capturePrefix)
        functions registry packet.header) budget := by
  obtain ⟨issuedProfiles⟩ := profiles packet accepted nativeMember functions origin complete wellFormed children
  exact CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.source_continuation
    functions origin.owner origin.capture_zero (origin.globals member) caller
    beforeTyped argumentsTyped stable wellFormed
    issuedProfiles
    (children []).syntaxTree budget below

include accepted nativeMember complete wellFormed children member beforeTyped argumentsTyped stable in
/-- Reflection retains strict native flow grades and the independent Source
grade returned by the original typed finish at that same parameter entry. -/
theorem native_continuation (budget : Nat)
    (below : Below budget (fun child => ∀ administrative
      (profile : Profile (certificates := certificates)
        (expressionSyntax := expressionSyntax) packet.header administrative),
      FlowReflects (registry := registry) (faults := faults) (headers := headers)
        functions origin.owner profile child)) :
    CallableIndexedOwnedInvocationBounds.NativeContinuation
      (functions := functions) (registry := registry) (faults := faults)
      (header := packet.header) (arguments := arguments) origin.owner caller
      (CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
        (locations := origin.owner.key.locations) (capturePrefix := origin.owner.key.capturePrefix)
        functions registry packet.header) budget := by
  obtain ⟨issuedProfiles⟩ := profiles packet accepted nativeMember functions origin complete wellFormed children
  exact CallableIndexedOwnedPreparedCatalogNamedBodyContinuations.native_continuation
    functions origin.owner origin.capture_zero (origin.globals member) caller
    beforeTyped argumentsTyped stable wellFormed
    issuedProfiles
    (children []).syntaxTree budget below

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedProfileFamilies
end
