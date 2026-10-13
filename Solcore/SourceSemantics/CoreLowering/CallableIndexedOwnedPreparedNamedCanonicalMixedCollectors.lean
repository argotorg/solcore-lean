import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedLexicalLambdaFormation

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

inductive Syntax (header : Header compiled (Program.ofChecked compiled.sourceProgram)) : ExpressionId → Prop where
  | general {id} (tree : GeneralSyntax header.function.source id) : Syntax header id
  | formation {id} (shape : ReturnLambda header id) : Syntax header id

variable {recipe : SourceCoreIndexedSession.Recipe}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)

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
    prepared aligned ready wellFormed complete zero member receipt
    (RecursiveNamedPreparedStageScopes.registry actual) syntaxTree
  intro child selected context fields scope fuel id node lowered declarations approved found typed accepted nativeType native
  have sameSource := (RecursiveNamedPreparedStageScopes.registry actual).source selected
  cases approved with
  | general tree =>
    obtain ⟨root, samePrefix⟩ := CallableIndexedOwnedPreparedStagedNamedCanonicalScopedRoots.of_accepted
      prepared aligned diagnostic receiver wellFormed metadata rows complete actual selected fields
      (by simpa only [sameSource] using declarations) (by simpa only [sameSource] using tree)
      (by simpa only [sameSource] using found) (by simpa only [sameSource] using typed)
      (by simpa only [sameSource] using accepted)
    exact .canonical root samePrefix
  | formation shape =>
    have sameNode : node = shape.node := Option.some.inj (found.symm.trans shape.found)
    subst node
    obtain ⟨formation⟩ := CallableIndexedOwnedPreparedNamedLexicalLambdaFormation.of_expression
      prepared aligned diagnostic wellFormed profile selected found shape.form shape.owner
      shape.requirements shape.coercions
      (by simpa only [aligned.named] using shape.ordinary) shape.read
      shape.returnFound shape.returnForm shape.returnType fields declarations typed accepted native
    obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
    have original : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
        header.function.context header.function.source := by
      rw [header.frame.context, header.frame.source]
      exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
    exact .legacy (.formation formation
      (by rw [sameSource]
          exact (original.transport (RecursiveNamedInitialContextValidity.mono_fields header.extended)).transport fields)
      (by rw [(RecursiveNamedPreparedStageScopes.registry actual).evidence selected]
          exact fields.covers (RecursiveNamedInitialContextValidity.covers header.frame header.extended)))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalMixedCollectors
