import Solcore.SourceSemantics.CoreLowering.ProtectedWhileEndpoint
import Solcore.SourceSemantics.CoreLowering.NamedWhileEdges
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileCertificates

/-! Concrete named condition and lexical/assignment Trees close finite while
head semantics and the generated self-cell envelope. Installed code, captures
and history stay explicit. Break/continue and nested loops are not in the body
profile; enclosing statement grammar and contextual extraction remain separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedWhileStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep ControlShape)

section Shape
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {values : ValuesContext}
  {source : TypedSource} {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
  {definitions : DataEnvironment} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

private theorem lexical_control_shape
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code) (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after) :
    ControlShape outcome := by
  induction tree generalizing actualContext finalContext environment before after outcome with
  | nil allowed =>
    obtain ⟨_, rfl, _⟩ := ScalarStatementViews.nil_view _ executed
    exact .fallthrough _
  | @returnUnit context scope mode id node rest found form =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      cases impossible
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.returnUnit unique contains form head
      exact .returned _
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType value =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ other; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head
      cases impossible
    · obtain ⟨_, result, rfl, _⟩ := ScalarStatementViews.returnValue unique contains form head
      exact .returned result
  | tail found form expressionFound valueType value =>
    cases executed with
    | tailExpression => exact .returned _
    | singleton contains notTail head =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
      subst_vars
      exact False.elim (notTail _ form)
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, rfl, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, _, _, rfl, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.block unique contains form head
      exact (innerIH innerTrace).restore environment
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view mode unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, boolean, _, _, innerOutcome, _, rfl, branchTrace⟩ := ScalarStatementViews.ifThen unique contains form head
      cases boolean with
      | false => exact (elseIH branchTrace).restore environment
      | true => exact (thenIH branchTrace).restore environment

  | terminalBlock exactUnique found form inner stops issued innerIH =>
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, terminal⟩
    · cases GenericLexicalStatements.block_terminates exactUnique found form stops head
    · obtain ⟨_, _, _, rfl, body⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form head
      exact (innerIH body).restore environment
  | terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨head, terminal⟩
    · cases GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops head
    · obtain ⟨_, boolean, _, _, _, _, rfl, body⟩ := ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form head
      cases boolean with
      | false => exact (elseIH body).restore environment
      | true => exact (thenIH body).restore environment

/-- Successful source control cannot stand for the separate fault judgment.
This is a structural inversion of the actual static body Tree. -/
theorem body_control_shape
    (tree : ProtectedLexicalAssignments.Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext outcome after) :
    ControlShape outcome := by
  induction tree generalizing actualContext finalContext environment before after outcome with
  | lexical fragment => exact lexical_control_shape fragment unique executed
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view _ unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, rfl, _⟩ := ScalarStatementViews.letUninitialized unique contains form head
      cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view _ unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, _, _, _, rfl, _, _⟩ := ScalarStatementViews.letInitialized unique contains form mono head
      cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view _ unique contains (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view _ unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, _, innerOutcome, rfl, innerTrace⟩ := ScalarStatementViews.block unique contains form head
      exact (innerIH innerTrace).restore environment
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view _ unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨head, terminal⟩
    · exact restIH tail
    · obtain ⟨_, boolean, _, _, innerOutcome, _, rfl, branchTrace⟩ := ScalarStatementViews.ifThen unique contains form head
      cases boolean with
      | false => exact (elseIH branchTrace).restore environment
      | true => exact (thenIH branchTrace).restore environment
  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head errors remaining ih =>
    have contains := lookupStatement?_sound found
    rcases ScalarStatementViews.cons_view _ unique contains (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨first, terminal⟩
    · exact ih tail
    · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique contains form first
      cases terminal

theorem body_control_not_fault
    (tree : ProtectedLexicalAssignments.Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (executed : ScalarStatementViews.ListExecutes mode program actualContext evidence source environment before statements finalContext (.fault reason) after) : False := by
  cases body_control_shape tree unique executed
end Shape


variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

variable {context : SourceSemantics.Context} {scope : Scope} {administrative : Core.Context}
  {type : Ty} {conditionCode bodyCode : Expr} {selfReason : Word}

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- All condition and body runtime obligations are discharged by the concrete
named Trees. The actual native head type is retained as a separate static fact. -/
theorem preserves {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (bodyTree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode bodyCode selfReason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedWhile.HeadPreserves functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      id expected type (LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  intro valid
  exact ProtectedWhile.while_preserves functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    found form conditionFound conditionTree typed unique
    (NamedLexicalAssignments.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing bodyTree) valid

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Native completion reconstructs the independent source head and its effects.
Successful body control excludes faults by static Tree inversion, rather than
by a caller-supplied body execution or universal semantic contract. -/
theorem reflects {id : StatementId} {node : StatementNode} {condition : ExpressionId} {conditionNode : ExpressionNode}
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
    (conditionFound : source.lookupExpression? condition = some conditionNode)
    (conditionTree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (bodyTree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type conditionCode bodyCode selfReason) (LocalLoop.resultType type) ambient.definitions) :
    ProtectedWhile.HeadReflects functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults) (solved := solved)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope)
      id expected type (LocalLoop.whileLoop type conditionCode bodyCode selfReason) := by
  intro valid
  exact ProtectedWhile.while_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    found form conditionFound conditionTree typed
    (NamedLexicalAssignments.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing bodyTree)
    (fun executed => body_control_not_fault bodyTree unique executed) valid

end Solcore.SourceSemantics.CoreLowering.NamedWhileStatements
