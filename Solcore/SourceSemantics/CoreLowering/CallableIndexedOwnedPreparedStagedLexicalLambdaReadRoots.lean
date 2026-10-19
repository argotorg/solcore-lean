import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaReadDiagnostics
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedHeaderPolicies

/-! Ordinary closure reads at real lexical contexts are recovered from actual
body callbacks. Original frames, declarations, metadata and issued diagnostic
provenance supply every static Root field; no execution law is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableLambdaBodyReachability CallableLambdaViewEdits
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls Syntax PolicyOn)
open CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles (MetadataFor MetadataOn)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots (OriginalAuthority)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt Root)
open CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts (Choice)

private theorem read_no_calls
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered)
    {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope} {callId callee : ExpressionId}
    {ids : List ExpressionId} {metadata : IndirectCallResolution} {code : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation source
      callScope callId callee ids metadata reasonAt code) (path : Calls compiler root) : False := by
  cases path with
  | here sequence children =>
    have identity := Option.some.inj (compiler.found.symm.trans found)
    have same := compiler.originalForm
    rw [identity, form] at same
    cases same
  | @method_child current id otherFuel code types outer sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    rcases outer.operator.form with ⟨operator, operand, otherForm, _⟩ | ⟨operator, left, right, otherForm, _⟩
    all_goals rw [identity, form] at otherForm; cases otherForm
  | @group current id other inner innerNode code actual otherForm innerFound type child inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @tuple_child current id other tupleIds types codes header sequence children child childCode member inside =>
    have identity := Option.some.inj (header.metadata.found.symm.trans found)
    have same := header.form
    rw [identity, form] at same
    cases same
  | @constructor_child current id other instantiation constructorIds tag headerWord codes header otherForm admissible ranges count nodes sequence children child childCode member inside =>
    have same := Option.some.inj (header.metadata.found.symm.trans found)
    subst other
    simp [form] at otherForm
  | @builtin_child current id otherCallee otherIds function otherFuel code outer calleeTyped sourceType nativeTypes sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    have same := outer.form
    rw [identity, form] at same
    cases same
  | @direct_child current id callee directIds instantiation fuel code types outer calleeTyped application sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.metadata.found.symm.trans found)
    have same := outer.form
    rw [identity, form] at same
    cases same
  | @call_child current id otherCallee otherIds otherMetadata otherFuel code types outer sequence children child childCode member inside =>
    have identity := Option.some.inj (outer.found.symm.trans found)
    have same := outer.originalForm
    rw [identity, form] at same
    cases same
  | @unary_child scope id node operand childNode operator operandType resultType core childCode actual otherForm childFound inputType outputType profile child inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode actual otherForm leftFound rightFound leftType rightType outputType profile first second inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode actual otherForm leftFound rightFound leftType rightType outputType profile first second inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode actual otherForm conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside =>
    have identity := Option.some.inj (actual.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm
  | @index_base scope id other base key baseNode keyNode layout comparison first second header keyFound otherForm sourceType firstTree secondTree inside
  | @index_key scope id other base key baseNode keyNode layout comparison first second header keyFound otherForm sourceType firstTree secondTree inside =>
    have identity := Option.some.inj (header.metadata.found.symm.trans found)
    rw [identity, form] at otherForm
    cases otherForm




/-- Reached view metadata follows from full original metadata and the exact
unchanged body footprint retained by this Code. -/
theorem viewed_metadata {compiled : SourceCoreUnifiedCompilation.Compiled}
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    {named : CallableIndexedNamedGeneration.Named}
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView code)
    (original : MetadataFor compiled.indexed named function.source) :
    MetadataOn compiled.indexed named code.view
      (fun id => Reaches code.view (function.body.map NodeId.statement) (.expression id)) := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids bodyView
  have originalTree : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      Syntax code.view id → Syntax function.source id := fun id reached tree =>
    CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.syntax_original edited avoids tree
      (reached.metadata code.viewOfSource.symm)
  have lookup : ∀ id, Reaches code.view (function.body.map NodeId.statement) (.expression id) →
      ∀ node, code.view.lookupExpression? id = some node → function.source.lookupExpression? id = some node :=
    fun id reached node found => (bodyView id (reached.metadata code.viewOfSource.symm)).trans found
  exact {
    requirements := fun id reached tree node found => original.requirements id (originalTree id reached tree) node (lookup id reached node found)
    coercions := fun id reached tree node found => original.coercions id (originalTree id reached tree) node (lookup id reached node found)
    initializer := fun id reached tree => original.initializer id (originalTree id reached tree)
    arguments := fun id reached tree node found => original.arguments id (originalTree id reached tree) node (lookup id reached node found)
    localRead := fun id reached tree node found => original.localRead id (originalTree id reached tree) node (lookup id reached node found) }

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {bodyRegistry : SourceCoreRawMetadata.Registry}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics))
  (provenance : CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code support)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (original : MetadataFor compiled.indexed support.caller.named function.source)
  {stages : Staging.Recursive.Registry} (choice : Choice code (stages := stages))

local notation "faults" => CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics

include provenance receiver wellFormed original in
/-- The Source lexical context is the exact context supplied by typed
compiler traversal, and diagnostics are restricted to this body's real reads. -/
theorem of_child
    {context : SourceSemantics.Context} {current : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope} (selected : stages.Closure function invocation)
    (fields : Dynamic.RuntimeContextFields support.body.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType function.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation code.view current id code.reasonAt = .ok lowered) :
    Nonempty (RootAt compiled context invocation current id lowered faults) := by
  let edited := CallableIndexedLambdaBodyViewEdits.local_view code.viewOfSource
  have avoids := CallableIndexedLambdaBodyViewEdits.avoids provenance.body_view
  have sourceProfile := (CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_for
    provenance.policy_recipe original current code.reasonAt).on
      (fun id => Reaches function.source (function.body.map NodeId.statement) (.expression id))
  have viewProfile := CallableIndexedOwnedPreparedStagedRecursiveCallerPolicyProfiles.retained_policy_on
    provenance.policy_recipe (viewed_metadata provenance.body_view original) current code.reasonAt
  have viewedFound : code.view.lookupExpression? id = some node :=
    (provenance.body_view id reached).symm.trans found
  have viewedTree : Syntax code.view id := .leaf (.read viewedFound form)
  have compiledChild := CallableIndexedOwnedPreparedStagedRecursiveBodyViewTransport.accepted_original_on
    edited avoids sourceProfile viewProfile code.callables fuel viewedTree reached accepted
  have sameSource := stages.source selected
  have unique : NodeOccurrencesUnique invocation.source := by rw [sameSource]; exact support.body.unique
  have childFound : invocation.source.lookupExpression? id = some node := by simpa only [sameSource] using found
  have childTyped : ExpressionHasType invocation.source context id node.type := by simpa only [sameSource] using typed
  have childProfile : PolicyOn code.policy code.compilation compiled.indexed.fuel
      (.initial compiled.compatible.checked) invocation.source current code.reasonAt
      (fun id => Reaches invocation.source (function.body.map NodeId.statement) (.expression id)) := by
    simpa only [sameSource] using sourceProfile
  have childDeclarations : CompatibleExpressionReads.ScopeDeclarations invocation.source current context := by
    simpa only [sameSource] using declarations
  have childTree : Syntax invocation.source id := .leaf (.read childFound form)
  have childReached : Reaches invocation.source (function.body.map NodeId.statement) (.expression id) := by
    simpa only [sameSource] using reached
  have childAccepted : SourceCoreFunctions.lowerExpressionWithPolicy code.policy code.lowerBody fuel
      code.compilation invocation.source current id code.reasonAt = .ok lowered := by
    simpa only [sameSource] using compiledChild
  have coercions : ∀ id node, Syntax invocation.source id →
      invocation.source.lookupExpression? id = some node → node.coercions = [] := by
    intro expression actual tree found
    exact original.coercions expression (by simpa only [sameSource] using tree) actual
      (by simpa only [sameSource] using found)
  let certificate := CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.of_functions_on
    unique childDeclarations childProfile (fun parent found edge => Reaches.expression parent found edge)
    (fun id node _ tree found => coercions id node tree found) childTree childReached childFound childTyped childAccepted
  have ready : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
      (compiled := compiled) (invocation := invocation) certificate := by
    intro callFuel callScope callId callee ids callMetadata code compiler path
    exact False.elim (read_no_calls childFound form certificate compiler path)
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1.transport fields
  let root : Root compiled code.policy code.lowerBody code.compilation compiled.indexed.fuel
      context invocation code.reasonAt current id lowered node.type faults := {
    compilerFuel := fuel
    accepted := childAccepted
    certificate := certificate
    node := node
    found := childFound
    rawResult := rfl
    typed := childTyped
    sameLedger := fields.solvedRequirements.trans support.body.valid.ledger
    runtimeLedger := fields.runtimeRequirementLedger support.body.valid.runtime
    unique := unique
    wellFormed := wellFormed
    runtime := by simpa only [sameSource] using runtime
    covers := by rw [stages.evidence selected]; exact fields.covers support.body.valid.covers
    actualFunctionType := by rw [code.callables]; rfl
    uninitialized := by
      intro current child lowered receipt path location
      exact CallableIndexedOwnedContextualLambdaReadDiagnostics.uninitialized support provenance.body_reasons receiver
        (Reaches.from_root reached (by simpa only [sameSource] using path))
        (by simpa only [sameSource] using receipt) location
    callsReady := ready
    noMethods := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_methods_of_policy_on _ childTree childReached childProfile
    noDirect := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_direct_of_syntax _ childTree
    noIndexes := CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax.no_indexes_of_syntax _ childTree }
  exact ⟨RootAt.ofRoot root⟩


include provenance receiver wellFormed original in
/-- The lexical packet is one actual caller of the shared read producer. -/
theorem of_accepted
    {context : SourceSemantics.Context} {current : SourceCoreLocalCell.Scope}
    {invocation : Staging.Recursive.Scope} (selected : stages.Closure function invocation)
    (fields : Dynamic.RuntimeContextFields support.body.context context)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source current context)
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    (reached : Reaches function.source (function.body.map NodeId.statement) (.expression id))
    (found : function.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType function.source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : choice.packet.policy.lowerExpression fuel code.view current id choice.packet.reasonAt = .ok lowered) :
    Nonempty (RootAt compiled context invocation current id lowered faults) := by
  apply of_child code support provenance receiver wellFormed original selected fields declarations reached found form typed
  simpa only [choice.callback, choice.reason, FunctionCode.children] using accepted


/-- The first lexical closure fragment permits any number of original reads. -/
def Read (source : TypedSource) (id : ExpressionId) : Prop :=
  ∃ node name binder, source.lookupExpression? id = some node ∧
    node.form = .reference name (.local binder)

include provenance receiver wellFormed original in
/-- The authentic original compiler traversal constructs every Root at its
real post-let context. The caller supplies only Source grammar facts. -/
def support_reads
    (syntaxTree : GenericLexicalStatements.Syntax function.source (Read function.source)
      support.body.context true function.body function.resultType) :
    CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.LexicalSupport
      code support.body.toContext stages choice.packet faults := by
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters
    support.body.frame support.body.extended).1
  have sourceSignatures : support.body.context.signatures = compiled.compatible.checked.signatures :=
    (runtime.signatures.trans
      (RecursiveNamedSelectedExpressionFactory.header_program_signatures
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed.ancestry) support.caller).symm).trans
      (RecursiveNamedPreparedHeaderPolicies.Prepared.header_signatures (header := support.caller))
  refine ⟨support.body.frame, support.body.projection, ?_⟩
  intro child selected
  have actual := CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerSupport.tree
    code support.body.toContext support.body.frame choice provenance.body_view provenance.scope_declarations
    sourceSignatures support.body.projection syntaxTree
    (certificates := fun context scope id lowered => Nonempty (RootAt compiled context child scope id lowered faults))
    (fun context fields current fuel id node lowered declarations read reached found typed accepted _nativeType _native => by
      obtain ⟨readNode, name, binder, readFound, form⟩ := read
      have same := Option.some.inj (readFound.symm.trans found)
      subst readNode
      exact of_accepted code support provenance receiver wellFormed original choice selected fields declarations
        reached found form typed accepted)
  simpa only [stages.source selected] using actual

include provenance receiver wellFormed original in
omit choice in
/-- A packet and its static support are chosen together inside Prop from the
retained lowerer. No classical selector or independently assumed Tree is used. -/
theorem of_reads
    {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
    (shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape function.source function.body)
    (syntaxTree : GenericLexicalStatements.Syntax function.source (Read function.source)
      support.body.context true function.body function.resultType)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Σ packet : CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Packet code stages,
      CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport.Support
        headers code support.body.toContext stages packet faults) := by
  obtain ⟨choice⟩ := CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts.choose
    code support.caller.named provenance.policy_recipe.body_recipe shape child selected
  exact ⟨⟨.lexical choice.packet,
    support_reads code support provenance receiver wellFormed original choice syntaxTree⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaReadRoots
