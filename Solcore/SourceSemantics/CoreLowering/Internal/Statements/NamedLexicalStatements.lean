import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.WhileLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalWhile
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.AssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BitNotStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedScopedControl
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LexicalStatements

/-!
# Named lexical statements

Lexical statements, assignments and `while` loops of named bodies, and their fault contracts.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedLexicalAssignments
/-! Concrete recursive named-call expression trees close lexical initializer,
condition, discarded and returned children at their actual source contexts.
Installed global code/captures/history are explicit entry facts. Loops and static named contextual-tree extraction remain separate; no runtime child meaning is an
external premise of these consumers. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLexicalAssignments
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open CallableIndexedHistory
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev Tree {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  ProtectedLexicalAssignments.Tree layouts owner active frame globals onError values source
    (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
    administrative ambient.definitions registry faults

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

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem Tree.preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedLexicalAssignments.ControlAt.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedLexicalAssignments.Tree.preserves functions definitions registered extension faithful observations program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    tree valid unique environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem Tree.reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedLexicalAssignments.ControlAt.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedLexicalAssignments.Tree.reflects functions definitions registered extension faithful observations runtimeViews program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun context valid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    tree valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

/-- Scoped restoration retains the old canonical caller environment while
transporting its actual observations through all heap/admin suffix effects. -/
theorem retained {scope : Scope} {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {before after : Dynamic.Heap} {store finalStore : Store} {canonical : Environment}
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope finalMap finalWorld after finalStore canonical :=
  (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix).extend installed maps worlds frame metadata

end Solcore.SourceSemantics.CoreLowering.NamedLexicalAssignments
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedWhileEdges
/-! Concrete named expression and lexical/assignment Trees close both while
edges at the actual caller context. Installed globals, exact captures and frame
histories remain separate runtime entry facts. This unit covers condition/body
edges, not full finite iterations, for post/initializers or contextual extraction.
The lexical body profile excludes break/continue and nested loops. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedWhileEdges
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open TypedLexicalWhile (Scope ValuesContext Progress FlowRep)
open TypedScopedStatements (Executes)
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

/-- Same installed authority as recursive named expression/statement consumers. -/
abbrev State (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry)
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) :=
  ProtectedWhile.State (NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
    values registry functions

variable {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode bodyCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- All condition child/body meaning follows from concrete accepted named Trees. -/
theorem condition_preserves
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason mapping world before store)
    {outcome : Dynamic.ExpressionOutcome}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
        (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason finalMap finalWorld after finalStore :=
  ProtectedWhile.condition_preserves functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
    tree found agrees state trace

include extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
/-- Actual condition completion reconstructs its source trace and retained entry. -/
theorem condition_reflects
    {condition : ExpressionId} {node : ExpressionNode}
    (tree : NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt scope condition ⟨.bool, conditionCode⟩)
    (found : source.lookupExpression? condition = some node)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.entryEnvironment type location actual) store
      (Core.LoopExecution.conditionCode (conditionCode.rename ξ)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before condition outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld node.type .bool faults outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type (conditionCode.rename ξ) bodyCode selfReason finalMap finalWorld after finalStore :=
  ProtectedWhile.condition_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing)
    tree found agrees state evaluated

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The concrete lexical body closes child meaning at every reached context;
its outer entry and body-local source context are retained separately. -/
theorem body_preserves
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (tree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason mapping world before store)
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (trace : Executes false program context evidence source environment before statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
        (Core.LoopExecution.bodyCode (bodyCode.rename ξ)) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after :=
  ProtectedWhile.body_preserves functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedLexicalAssignments.Tree.preserves functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing tree)
    valid agrees reference state trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The concrete lexical body closes child meaning at every reached context;
its outer entry and body-local source context are retained separately. -/
theorem body_reflects
    {statements : List StatementId} {expected : TypeSystem.Ty}
    (tree : NamedLexicalAssignments.Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      administrative registry faults context scope false statements expected type bodyCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (state : State functions registry bodies compilation context scope administrative actualContext frame
      environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason mapping world before store)
    {value : Value} {finalStore : Store}
    (evaluated : Evaluates (Core.LoopExecution.bodyEnvironment type location actual) store
      (Core.LoopExecution.bodyCode (bodyCode.rename ξ)) value finalStore) :
    ∃ finalContext outcome after finalMap finalWorld,
      Executes false program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      State functions registry bodies compilation context scope administrative actualContext frame
        environment canonical actual contextLocation location type conditionCode (bodyCode.rename ξ) selfReason finalMap finalWorld after finalStore ∧
      TypedLexicalControl.LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after :=
  ProtectedWhile.body_reflects functions program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedLexicalAssignments.Tree.reflects functions definitions registered extension faithful observations runtimeViews evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing tree)
    valid agrees reference state evaluated

end Solcore.SourceSemantics.CoreLowering.NamedWhileEdges
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedWhileStatements
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedLexicalFlowFaultPostContracts
/-! Fault posts remain beside each actual ready tuple. These interfaces neither
choose an execution nor provide a finished lexical or function meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLexicalFlowFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements (FlowRep)
open GenericLexicalStatements (Scope ValuesContext)
open TypedLexicalControl (Restored LexicalResult)
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
universe u v

abbrev HeadFaultPost := Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → StatementId → Dynamic.SemanticFault →
  Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

abbrev FlowFaultPost := Program → SourceSemantics.Context → Dynamic.EvidenceEnvironment →
  TypedSource → Dynamic.Environment → Dynamic.Heap → Bool → List StatementId → Dynamic.SemanticFault →
  Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop

def HeadOutcomePost (post : HeadFaultPost) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : StatementId) (type : Core.Ty)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) (result : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .fault reason => ∃ token, result = .inLeft (LocalLoop.controlType type) (.word token) ∧
      post program context evidence source environment before id reason after token mapping world store
  | _ => True

def FlowOutcomePost (post : FlowFaultPost) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (mode : Bool) (statements : List StatementId) (type : Core.Ty)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) (result : Value)
    (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  match outcome with
  | .fault reason => ∃ token, result = .inLeft (LocalLoop.controlType type) (.word token) ∧
      post program context evidence source environment before mode statements reason after token mapping world store
  | _ => True

def TrivialHead : HeadFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True
def TrivialFlow : FlowFaultPost := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True

/-- The owning statement form is retained by the expression-to-head edge. -/
inductive ExpressionHeadLink (source : TypedSource) (id : StatementId) : ExpressionId → Prop where
  | returning {node expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression)) : ExpressionHeadLink source id expression
  | expression {node expression semicolon} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression semicolon) : ExpressionHeadLink source id expression
  | initialized {node binder expression} (found : source.lookupStatement? id = some node)
      (form : node.form = .letDecl binder (some expression)) (mono : binder.scheme.quantified = []) :
      ExpressionHeadLink source id expression
  | condition {node expression thenBody elseBody} (found : source.lookupStatement? id = some node)
      (form : node.form = .ifThen expression thenBody elseBody) : ExpressionHeadLink source id expression

mutual
/-- A causal head path is constructed at the actual semantic join. -/
inductive HeadOrigin (post : ExpressionFailurePostContracts.ExpressionFaultPost)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SourceSemantics.Context → Dynamic.Environment → Dynamic.Heap → StatementId →
    Dynamic.SemanticFault → Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop where
  | expression {context environment before id expression reason after token mapping world store}
      (link : ExpressionHeadLink source id expression)
      (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
      (retained : post program context evidence source environment before expression reason after token mapping world store) :
      HeadOrigin post program evidence source context environment before id reason after token mapping world store
  | block {context environment before id node statements reason after token mapping world store}
      (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
      (retained : FlowOrigin post program evidence source context environment before false statements reason after token mapping world store) :
      HeadOrigin post program evidence source context environment before id reason after token mapping world store
  | selected {context environment before middle id node expression thenBody elseBody boolean reason after token mapping world store}
      (found : source.lookupStatement? id = some node) (form : node.form = .ifThen expression thenBody elseBody)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before expression (.bool boolean) middle)
      (retained : FlowOrigin post program evidence source context environment middle false
        (if boolean then thenBody else elseBody.getD []) reason after token mapping world store) :
      HeadOrigin post program evidence source context environment before id reason after token mapping world store
/-- Prefix constructors retain the executed Source statement and literal middle configuration. -/
inductive FlowOrigin (post : ExpressionFailurePostContracts.ExpressionFaultPost)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SourceSemantics.Context → Dynamic.Environment → Dynamic.Heap → Bool → List StatementId →
    Dynamic.SemanticFault → Dynamic.Heap → Word → LocationMap → StoreTyping → Store → Prop where
  | head {context environment before mode id rest reason after token mapping world store}
      (retained : HeadOrigin post program evidence source context environment before id reason after token mapping world store) :
      FlowOrigin post program evidence source context environment before mode (id :: rest) reason after token mapping world store
  | tailExpression {context environment before id node expression reason after token mapping world store}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
      (retained : post program context evidence source environment before expression reason after token mapping world store) :
      FlowOrigin post program evidence source context environment before true [id] reason after token mapping world store
  | prefix {context nextContext environment next before middle mode id rest reason after token mapping world store}
      (executed : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough next) middle)
      (retained : FlowOrigin post program evidence source nextContext next middle mode rest reason after token mapping world store) :
      FlowOrigin post program evidence source context environment before mode (id :: rest) reason after token mapping world store
end

abbrev HeadPost (post : ExpressionFailurePostContracts.ExpressionFaultPost) : HeadFaultPost :=
  fun program context evidence source environment before id reason after token mapping world store =>
    HeadOrigin post program evidence source context environment before id reason after token mapping world store
abbrev FlowPost (post : ExpressionFailurePostContracts.ExpressionFaultPost) : FlowFaultPost :=
  fun program context evidence source environment before mode statements reason after token mapping world store =>
    FlowOrigin post program evidence source context environment before mode statements reason after token mapping world store

/-- Finite causal-edge laws. These laws provide no lexical evaluations. -/
structure Joins (expressionPost : ExpressionFailurePostContracts.ExpressionFaultPost)
    (headPost : HeadFaultPost) (flowPost : FlowFaultPost)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  expression : ∀ {context environment before id expression reason after token mapping world store},
    ExpressionHeadLink source id expression →
    Dynamic.ExpressionFaults program context evidence source environment before expression reason after →
    expressionPost program context evidence source environment before expression reason after token mapping world store →
    headPost program context evidence source environment before id reason after token mapping world store
  tailExpression : ∀ {context environment before id node expression reason after token mapping world store},
    source.lookupStatement? id = some node → node.form = .expression expression false →
    Dynamic.ExpressionFaults program context evidence source environment before expression reason after →
    expressionPost program context evidence source environment before expression reason after token mapping world store →
    flowPost program context evidence source environment before true [id] reason after token mapping world store
  head : ∀ {context environment before mode id rest reason after token mapping world store},
    headPost program context evidence source environment before id reason after token mapping world store →
    flowPost program context evidence source environment before mode (id :: rest) reason after token mapping world store
  prefixFault : ∀ {context nextContext environment next before middle mode id rest reason after token mapping world store},
    Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough next) middle →
    flowPost program nextContext evidence source next middle mode rest reason after token mapping world store →
    flowPost program context evidence source environment before mode (id :: rest) reason after token mapping world store
  block : ∀ {context environment before id node statements reason after token mapping world store},
    source.lookupStatement? id = some node → node.form = .block statements →
    flowPost program context evidence source environment before false statements reason after token mapping world store →
    headPost program context evidence source environment before id reason after token mapping world store
  selected : ∀ {context environment before middle id node expression thenBody elseBody boolean reason after token mapping world store},
    source.lookupStatement? id = some node → node.form = .ifThen expression thenBody elseBody →
    Dynamic.ExpressionEvaluates program context evidence source environment before expression (.bool boolean) middle →
    flowPost program context evidence source environment middle false
      (if boolean then thenBody else elseBody.getD []) reason after token mapping world store →
    headPost program context evidence source environment before id reason after token mapping world store

theorem origin_joins (post : ExpressionFailurePostContracts.ExpressionFaultPost)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins post (HeadPost post) (FlowPost post) program evidence source where
  expression := .expression
  tailExpression := .tailExpression
  head := .head
  prefixFault := .prefix
  block := .block
  selected := .selected

theorem trivial_joins (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    Joins ExpressionFailurePostContracts.TrivialExpressionPost TrivialHead TrivialFlow program evidence source where
  expression := by intros; trivial
  tailExpression := by intros; trivial
  head := by intros; trivial
  prefixFault := by intros; trivial
  block := by intros; trivial
  selected := by intros; trivial

section CausalJoins
variable {post : ExpressionFailurePostContracts.ExpressionFaultPost}
  {headPost : HeadFaultPost} {flowPost : FlowFaultPost}
  {program : Program} {context nextContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment next : Dynamic.Environment} {before middle after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {statements rest thenBody : List StatementId}
  {elseBody : Option (List StatementId)} {expression : ExpressionId} {type : Ty}
  {outcome : Dynamic.ControlOutcome} {value : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store}

theorem head_to_flow (joins : Joins post headPost flowPost program evidence source) (retained : HeadOutcomePost headPost program context evidence source environment before id type outcome after value mapping world store)
    (mode : Bool) (rest : List StatementId) :
    FlowOutcomePost flowPost program context evidence source environment before mode (id :: rest) type outcome after value mapping world store := by
  cases outcome <;> try trivial
  obtain ⟨token, same, origin⟩ := retained
  exact ⟨token, same, joins.head origin⟩

theorem prefix_to_flow (joins : Joins post headPost flowPost program evidence source) {mode : Bool}
    (executed : Dynamic.StatementExecutes program context evidence source environment before id nextContext (.fallthrough next) middle)
    (retained : FlowOutcomePost flowPost program nextContext evidence source next middle mode rest type outcome after value mapping world store) :
    FlowOutcomePost flowPost program context evidence source environment before mode (id :: rest) type outcome after value mapping world store := by
  cases outcome <;> try trivial
  obtain ⟨token, same, origin⟩ := retained
  exact ⟨token, same, joins.prefixFault executed origin⟩

theorem block_to_head (joins : Joins post headPost flowPost program evidence source) (found : source.lookupStatement? id = some node) (form : node.form = .block statements)
    (retained : FlowOutcomePost flowPost program context evidence source environment before false statements type outcome after value mapping world store) :
    HeadOutcomePost headPost program context evidence source environment before id type
      (Dynamic.restoreControl environment outcome) after value mapping world store := by
  cases outcome <;> try trivial
  obtain ⟨token, same, origin⟩ := retained
  exact ⟨token, same, joins.block found form origin⟩

theorem selected_to_head (joins : Joins post headPost flowPost program evidence source) {boolean : Bool}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen expression thenBody elseBody)
    (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before expression (.bool boolean) middle)
    (retained : FlowOutcomePost flowPost program context evidence source environment middle false
      (if boolean then thenBody else elseBody.getD []) type outcome after value mapping world store) :
    HeadOutcomePost headPost program context evidence source environment before id type
      (Dynamic.restoreControl environment outcome) after value mapping world store := by
  cases outcome <;> try trivial
  obtain ⟨token, same, origin⟩ := retained
  exact ⟨token, same, joins.selected found form evaluated origin⟩
theorem expression_to_head (joins : Joins post headPost flowPost program evidence source)
    (link : ExpressionHeadLink source id expression) {reason : Dynamic.SemanticFault} {expressionType : Ty} {token : Word}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
    (retained : ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before expression expressionType
      (.fault reason) after (.inLeft expressionType (.word token)) mapping world store) :
    HeadOutcomePost headPost program context evidence source environment before id type (.fault reason) after
      (.inLeft (LocalLoop.controlType type) (.word token)) mapping world store := by
  obtain ⟨word, same, origin⟩ := retained
  have tokenSame : token = word := by injection same with _ same; injection same
  subst word
  exact ⟨token, rfl, joins.expression link failed origin⟩

theorem expression_to_flow (joins : Joins post headPost flowPost program evidence source)
    (link : ExpressionHeadLink source id expression) {reason : Dynamic.SemanticFault} {expressionType : Ty} {token : Word}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
    (retained : ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before expression expressionType
      (.fault reason) after (.inLeft expressionType (.word token)) mapping world store)
    (mode : Bool) (rest : List StatementId) :
    FlowOutcomePost flowPost program context evidence source environment before mode (id :: rest) type (.fault reason) after
      (.inLeft (LocalLoop.controlType type) (.word token)) mapping world store := by
  exact head_to_flow joins (expression_to_head joins link failed retained) mode rest

theorem tail_to_flow (joins : Joins post headPost flowPost program evidence source)
    (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
    {reason : Dynamic.SemanticFault} {expressionType : Ty} {token : Word}
    (failed : Dynamic.ExpressionFaults program context evidence source environment before expression reason after)
    (retained : ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before expression expressionType
      (.fault reason) after (.inLeft expressionType (.word token)) mapping world store) :
    FlowOutcomePost flowPost program context evidence source environment before true [id] type (.fault reason) after
      (.inLeft (LocalLoop.controlType type) (.word token)) mapping world store := by
  obtain ⟨word, same, origin⟩ := retained
  have tokenSame : token = word := by injection same with _ same; injection same
  subst word
  exact ⟨token, rfl, joins.tailExpression found form failed origin⟩

end CausalJoins

variable {Records : Type v}
variable (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {values : ValuesContext}
  {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}

def PreservesAtFor (post : FlowFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : RecursiveNamedLoopContracts.ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      FlowOutcomePost post program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore

def ReflectsAtFor (post : FlowFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      FlowOutcomePost post program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore

def HeadPreservesAtFor (post : HeadFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : headFacts context id expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : RecursiveNamedLoopContracts.StatementOutcome program size context evidence source environment before id finalContext outcome after),
    finalContext = context ∧ Restored environment outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      HeadOutcomePost post program context evidence source environment before id type outcome after value finalMap finalWorld finalStore

def HeadReflectsAtFor (post : HeadFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) {scope : Scope} (id : StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : headFacts context id expected)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : CoreProof.EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedLoopContracts.StatementOutcome program sourceSize context evidence source environment before id context outcome after ∧
      Restored environment outcome ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      HeadOutcomePost post program context evidence source environment before id type outcome after value finalMap finalWorld finalStore

section Expressions
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (certificate : GenericExpressionMeaning.Certificate)

def ExpressionPreservesAt (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → exprFacts context id node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ExpressionPost protocol readiness context node.type outcome reached) ∧
      ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before id
        lowered.type outcome after value finalMap finalWorld finalStore

def ExpressionReflectsAt (post : ExpressionFailurePostContracts.ExpressionFaultPost) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node → exprFacts context id node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      (∃ reached : protocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        protocol.Relates initial reached ∧ ExpressionPost protocol readiness context node.type outcome reached) ∧
      ExpressionFailurePostContracts.OutcomePost post program context evidence source environment before id
        lowered.type outcome after value finalMap finalWorld finalStore
end Expressions

section Trivial
variable {mode : Bool} {statements : List StatementId} {id : StatementId} {type : Ty}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ControlOutcome}
  {result : Value} {mapping : LocationMap} {world : StoreTyping} {store : Store} {expected : TypeSystem.Ty}

theorem FlowOutcomePost.of_trivial
    (represented : FlowRep (registry := registry) functions mapping world faults expected type outcome result) :
    FlowOutcomePost TrivialFlow program context evidence source environment before mode statements type outcome after result mapping world store := by
  cases represented <;> try trivial
  exact ⟨_, rfl, trivial⟩

theorem HeadOutcomePost.of_trivial
    (represented : FlowRep (registry := registry) functions mapping world faults expected type outcome result) :
    HeadOutcomePost TrivialHead program context evidence source environment before id type outcome after result mapping world store := by
  cases represented <;> try trivial
  exact ⟨_, rfl, trivial⟩
end Trivial

theorem PreservesAtFor.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    PreservesAtFor (post := TrivialFlow) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, FlowOutcomePost.of_trivial functions program evidence represented⟩

theorem PreservesAtFor.forget {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : PreservesAtFor (post := post) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.PreservesAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩

theorem ReflectsAtFor.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    ReflectsAtFor (post := TrivialFlow) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, FlowOutcomePost.of_trivial functions program evidence represented⟩

theorem ReflectsAtFor.forget {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ReflectsAtFor (post := post) protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.ReflectsAtFor protocol readiness condition facts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached⟩

theorem HeadPreservesAtFor.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code) :
    HeadPreservesAtFor (post := TrivialHead) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, HeadOutcomePost.of_trivial functions program evidence represented⟩

theorem HeadPreservesAtFor.forget {post : HeadFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : HeadPreservesAtFor (post := post) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.HeadPreservesAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  obtain ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady trace
  exact ⟨same, restores, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩

theorem HeadReflectsAtFor.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code) :
    HeadReflectsAtFor (post := TrivialHead) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached, HeadOutcomePost.of_trivial functions program evidence represented⟩

theorem HeadReflectsAtFor.forget {post : HeadFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope} {id : StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : HeadReflectsAtFor (post := post) protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code) :
    RecursiveNamedLexicalContracts.Stateful.WithReady.HeadReflectsAtFor protocol readiness condition headFacts (validity := validity) functions program evidence (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) id expected type code := by
  intro valid sourceFacts mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned initialReady evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, restores, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩

section ExpressionTrivial
variable (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (certificate : GenericExpressionMeaning.Certificate)
theorem ExpressionPreservesAt.of_trivial {size : Nat}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt protocol readiness program evidence model exprFacts certificate (context := context) (source := source) (faults := faults) size) :
    ExpressionPreservesAt (post := ExpressionFailurePostContracts.TrivialExpressionPost) protocol readiness program evidence model exprFacts certificate (context := context) (source := source) (faults := faults) size := by
  intro scope id lowered admitted node found facts mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after environments heaps locals agrees typed initial ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ := meaning admitted found facts environments heaps locals agrees typed initial ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition, ExpressionFailurePostContracts.OutcomePost.of_trivial represented⟩

theorem ExpressionReflectsAt.of_trivial {size : Nat}
    (meaning : RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionReflectsAt protocol readiness program evidence model exprFacts certificate (context := context) (source := source) (faults := faults) size) :
    ExpressionReflectsAt (post := ExpressionFailurePostContracts.TrivialExpressionPost) protocol readiness program evidence model exprFacts certificate (context := context) (source := source) (faults := faults) size := by
  intro scope id lowered admitted node found facts mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore environments heaps locals agrees typed initial ready evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ := meaning admitted found facts environments heaps locals agrees typed initial ready evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, transition, ExpressionFailurePostContracts.OutcomePost.of_trivial represented⟩

end ExpressionTrivial

end Solcore.SourceSemantics.CoreLowering.NamedLexicalFlowFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedLexicalFunctionFaultPostContracts
/-! The lexical post embeds into the actual five-way flow tuple and remains
at the same fault token and store through the existing function finish. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLexicalFunctionFaultPostContracts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext FlowRep Restored)
open TypedLexicalControl (LexicalResult)
open RecursiveNamedLoopContracts (ExecutesAt)
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
open NamedLexicalFlowFaultPostContracts
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (readiness : Readiness protocol) (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}

def PreservesAtWith (post : FlowFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_trace : ExecutesAt size mode program context evidence source environment before statements finalContext outcome after),
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      FlowOutcomePost post program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore

def ReflectsAtWith (post : FlowFaultPost) (validity : SourceSemantics.Context → Prop) (size : Nat) (mode : Bool) {scope : Scope} (statements : List StatementId) (expected : TypeSystem.Ty) (type : Ty) (code : Expr)
    : Prop :=
  ∀ (_valid : validity context)
    (_facts : facts context mode statements expected)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : CallableIndexedHistory.NativeFrame} {value : Value}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_condition : condition contextLocation native)
    (_ready : readiness.Ready context initial)
    (_evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore),
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements finalContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment finalContext after ∧
      Reached readiness context outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      FlowOutcomePost post program context evidence source environment before mode statements type outcome after value finalMap finalWorld finalStore


theorem PreservesAtWith.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code) :
    PreservesAtWith (post := TrivialFlow) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, readyPost⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, readyPost⟩, by cases represented <;> simp [FlowOutcomePost, TrivialFlow]⟩

theorem PreservesAtWith.forget {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : PreservesAtWith (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, readyPost⟩, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, readyPost⟩

theorem PreservesAtWith.of_lexical {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : NamedLexicalFlowFaultPostContracts.PreservesAtFor (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    PreservesAtWith (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, origin⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, TypedLexicalWhile.FlowRep.of_lexical represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, origin⟩

theorem ReflectsAtWith.of_trivial {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code) :
    ReflectsAtWith (post := TrivialFlow) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, readyPost⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, readyPost⟩, by cases represented <;> simp [FlowOutcomePost, TrivialFlow]⟩

theorem ReflectsAtWith.forget {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : ReflectsAtWith (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, ⟨reached, retained, readyPost⟩, _⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, retained, readyPost⟩

theorem ReflectsAtWith.of_lexical {post : FlowFaultPost} {validity : SourceSemantics.Context → Prop} {size : Nat} {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (meaning : NamedLexicalFlowFaultPostContracts.ReflectsAtFor (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) size (scope := scope) mode statements expected type code) :
    ReflectsAtWith (post := post) protocol readiness condition facts functions program evidence (validity := validity) (source := source) (context := context) (registry := registry) (faults := faults) (frameLayout := frameLayout) (globals := globals) (administrative := administrative) size (scope := scope) mode statements expected type code := by
  intro valid sourceFacts mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, origin⟩ := meaning valid sourceFacts environments heaps locals agrees actualTyped reference read unmapped initial conditioned ready evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, TypedLexicalWhile.FlowRep.of_lexical represented, finalHeaps, maps, worlds, frame, metadata, lexical, reached, origin⟩

/-- A finished post keeps the actual flow witness and exit. Direct transfer
exits carry no assertion about a primitive fault origin. -/
def FinishedPost (post : FlowFaultPost) (program : Program) (function : Dynamic.Closure)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (size : Nat) (type : Ty) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (result : Value) (mapping : LocationMap) (world : StoreTyping) (store : Store) : Prop :=
  ∃ finalContext control,
    RecursiveNamedLoopContracts.ExecutesAt size true program context function.evidence function.source
      environment before function.body finalContext control after ∧
    CompatibleNamedBody.Exit function.resultType control outcome ∧
    match control with
    | .fault reason => ∃ token, result = .inLeft type (.word token) ∧
        post program context function.evidence function.source environment before true function.body reason after token mapping world store
    | _ => True

theorem finished_post {post : FlowFaultPost} {program : Program} {function : Dynamic.Closure}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {size : Nat} {type : Ty} {control : Dynamic.ControlOutcome} {outcome : Dynamic.ExpressionOutcome}
    {input result : Value} {mapping : LocationMap} {world : StoreTyping} {initialStore finalStore : Store}
    {actual : Environment} {flow : Expr} {fellThrough escaped : Word}
    (trace : RecursiveNamedLoopContracts.ExecutesAt size true program context function.evidence function.source
      environment before function.body finalContext control after)
    (exit : CompatibleNamedBody.Exit function.resultType control outcome)
    (origin : FlowOutcomePost post program context function.evidence function.source environment before true function.body
      type control after input mapping world finalStore)
    (evaluated : Evaluates actual initialStore flow input finalStore)
    (completed : Evaluates actual initialStore (CompatibleStatements.finish type flow fellThrough escaped) result finalStore) :
    FinishedPost post program function context environment before size type outcome after result mapping world finalStore := by
  refine ⟨finalContext, control, trace, exit, ?_⟩
  cases control <;> try trivial
  obtain ⟨token, rfl, retained⟩ := origin
  obtain ⟨same, _⟩ := evaluation_deterministic completed
    (LocalControl.finish_failure _ (LocalLoop.toControl_failure _ escaped evaluated))
  exact ⟨token, same, retained⟩

end Solcore.SourceSemantics.CoreLowering.NamedLexicalFunctionFaultPostContracts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedAssignmentStatementTail
/-! Fixed lexical scope permits projected assignment, discarded expressions and
ordinary returns. Static named-call trees close all child/body meanings. Actual
installed globals/current history remain a guarded runtime entry condition. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentTails
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedScopedStatements
abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

inductive Tree (values : ValuesContext) (source : TypedSource) (context : SourceSemantics.Context)
    (certificate : GenericExpressionMeaning.Certificate) (scope : Scope)
    (administrative : Core.Context) (definitions : DataEnvironment) :
    Bool → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | nil {mode expected type} (allowed : mode = false ∨ expected = .unit) :
      Tree values source context certificate scope administrative definitions mode [] expected type (LocalLoop.fallthrough type)
  | returnUnit {mode id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
      Tree values source context certificate scope administrative definitions mode (id :: rest) .unit .unit (LocalLoop.returned .unit)
  | returnValue {mode id node expression expressionNode expected lowered} (rest : List StatementId)
      (found : source.lookupStatement? id = some node) (form : node.form = .returnStmt (some expression))
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : certificate scope expression lowered) :
      Tree values source context certificate scope administrative definitions mode (id :: rest) expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | tail {id node expression expressionNode expected lowered}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (valueType : expressionNode.type = expected)
      (value : certificate scope expression lowered) :
      Tree values source context certificate scope administrative definitions true [id] expected lowered.type
        (LocalLoop.returnValue lowered.type lowered.expression)
  | discard {mode id node expression expressionNode semicolon rest expected lowered type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
      (notTail : (!semicolon && mode && rest.isEmpty) = false)
      (expressionFound : source.lookupExpression? expression = some expressionNode)
      (value : certificate scope expression lowered)
      (remaining : Tree values source context certificate scope administrative definitions mode rest expected type body) :
      Tree values source context certificate scope administrative definitions mode (id :: rest) expected type
        (LocalSequence.discard (LocalLoop.controlType type) lowered.expression body)

  | assignment {mode id node assignment operator rhs rest expected type body}
      (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
      (head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs)
      (projected : head.prepared.steps ≠ [])
      (remaining : Tree values source context certificate scope administrative definitions mode rest expected type body) :
      Tree values source context certificate scope administrative definitions mode (id :: rest) expected type
        (head.emit body (LocalLoop.controlType type))

/-- The real production callback determines the assignment head and its exact
continuation expression. Only actual key/RHS lowering receipts are requested. -/
theorem Tree.of_assignment_lower {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate} {reasonAt : ExpressionId → Word}
    {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {expression : SourceCoreCompatibleDataPlaces.ExpressionLowerer} {fuel : Nat} {site : SourceCoreElaboration.ErrorSite}
    {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    {expected : TypeSystem.Ty} {type result : Ty} {next code : Expr}
    {invalidProjection invalidOperand : Word} {missing : TypeSystem.Ty → Word}
    (found : source.lookupStatement? id = some node) (form : node.form = .assignValue assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = values.checked.signatures)
    (sourceTyped : ∀ binder, SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root = .ok binder →
      SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type)
    (writable : ∀ binder, SourceCoreCompatibleDataPlaces.rootBinder source assignment.target.root = .ok binder →
      WritableLocal context assignment.target.root binder.scheme.body)
    (rightTyped : ExpressionHasType source context rhs assignment.target.type)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
      SourceCoreRawMetadata.runtimeType assignment.target.type = .integer ∧ operator.wordOnly = false)
    (extract : ∀ child lowered, child ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
      expression fuel source scope child reasonAt = .ok lowered → ∃ childNode,
      source.lookupExpression? child = some childNode ∧ certificate scope child lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions)
    (accepted : SourceCoreCompatibleDataPlaces.lower values values.checked.signatures expression fuel source scope site
      assignment operator (some rhs) (LocalLoop.controlType type) next reasonAt invalidProjection invalidOperand missing = .ok code)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code result definitions)
    (tail : Tree values source context certificate scope administrative definitions mode rest expected type next) :
    Tree values source context certificate scope administrative definitions mode (id :: rest) expected type code := by
  obtain ⟨head, same⟩ := GenericAssignmentStatements.Head.of_lower unique signatures sourceTyped writable rightTyped profile extract accepted typed
  have project : ∀ {codes leaf}, GenericAssignmentStatements.Shape values source context certificate scope
      administrative definitions assignment.target head.prepared codes leaf → head.prepared.steps ≠ [] := by
    intro codes leaf shape
    cases shape with
    | bare empty _ => exact False.elim (projected empty)
    | projected layout _ => exact layout.nonempty
  have nonempty := project head.shape
  rw [same]
  exact .assignment found form head nonempty tail

namespace Tree
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {scope : Scope} {administrative : Core.Context} {definitions : DataEnvironment}

inductive Errors (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :
    {mode : Bool} → {statements : List StatementId} → {expected : TypeSystem.Ty} → {type : Ty} → {code : Expr} →
      Tree values source context certificate scope administrative definitions mode statements expected type code → Prop where
  | nil {mode : Bool} {expected : TypeSystem.Ty} {type : Ty} {allowed : mode = false ∨ expected = .unit} :
      Errors registry faults (.nil (type := type) allowed)
  | returnUnit {mode id node rest} {found : source.lookupStatement? id = some node}
      {form : node.form = .returnStmt none} :
      Errors registry faults (.returnUnit (mode := mode) rest found form)
  | returnValue {mode id node expression expressionNode expected lowered rest}
      {found : source.lookupStatement? id = some node} {form : node.form = .returnStmt (some expression)}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {valueType : expressionNode.type = expected} {value : certificate scope expression lowered} :
      Errors registry faults (.returnValue (mode := mode) rest found form expressionFound valueType value)
  | tail {id node expression expressionNode expected lowered}
      {found : source.lookupStatement? id = some node} {form : node.form = .expression expression false}
      {expressionFound : source.lookupExpression? expression = some expressionNode}
      {valueType : expressionNode.type = expected} {value : certificate scope expression lowered} :
      Errors registry faults (.tail found form expressionFound valueType value)
  | discard {mode id node expression expressionNode semicolon rest expected lowered type body}
      {found : source.lookupStatement? id = some node} {form : node.form = .expression expression semicolon}
      {notTail : (!semicolon && mode && rest.isEmpty) = false}
      {expressionFound : source.lookupExpression? expression = some expressionNode} {value : certificate scope expression lowered}
      {remaining : Tree values source context certificate scope administrative definitions mode rest expected type body}
      (remainingErrors : Errors registry faults remaining) :
      Errors registry faults (.discard found form notTail expressionFound value remaining)
  | assignment {mode id node assignment operator rhs rest expected type body}
      {found : source.lookupStatement? id = some node} {form : node.form = .assignValue assignment operator rhs}
      {head : GenericAssignmentStatements.Head values source context certificate scope administrative definitions assignment operator rhs}
      {projected : head.prepared.steps ≠ []}
      {remaining : Tree values source context certificate scope administrative definitions mode rest expected type body}
      (headErrors : head.Errors registry faults) (remainingErrors : Errors registry faults remaining) :
      Errors registry faults (.assignment found form head projected remaining)
end Tree

section Source
variable {program : Program} {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId} {outcome : Dynamic.ControlOutcome}

private theorem nil_executes (mode : Bool) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Executes mode program context evidence source environment heap [] context (.fallthrough environment) heap := by
  cases mode <;> exact .control .nil

private theorem return_unit_view
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt none)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head; cases impossible
    · exact ScalarStatementViews.returnUnit unique contains form head
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨_, head⟩ | ⟨_, _, _, head, _⟩
    · exact False.elim (ScalarStatementViews.returnUnit_cannot_fault unique contains form head)
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.returnUnit unique contains form head; cases impossible

private theorem return_value_view {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .returnStmt (some expression))
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    finalContext = context ∧ ∃ expressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) := by
  have notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false := by
    intro _ _ expression; simp [form]
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains notTail executed with ⟨_, _, _, head, _⟩ | ⟨head, _⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head; cases impossible
    · obtain ⟨same, value, rfl, child⟩ := ScalarStatementViews.returnValue unique contains form head
      exact ⟨same, _, .value child, rfl⟩
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains notTail failed with ⟨same, head⟩ | ⟨_, _, _, head, _⟩
    · exact ⟨same, _, .fault (ScalarStatementViews.returnValue_fault unique contains form head), rfl⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique contains form head; cases impossible

private theorem tail_view {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression false)
    (trace : Dynamic.FunctionStatementsExecuteOutcome program context evidence source environment before [id] finalContext outcome after) :
    finalContext = context ∧ ∃ expressionOutcome,
      Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before expression expressionOutcome after ∧
      outcome = (match expressionOutcome with | .value value => .returned value | .fault reason => .fault reason) := by
  have shape : ∀ other, ContainsStatement source id other → other = node := by
    intro other present
    exact Option.some.inj ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases trace with
  | control executed => cases executed with
    | tailExpression present same child =>
      rw [shape _ present, form] at same
      cases same
      exact ⟨rfl, _, .value child, rfl⟩
    | singleton present notTail _ =>
      have eq := shape _ present; subst_vars
      exact False.elim (notTail expression form)
  | fault failed => cases failed with
    | tailExpression present same child =>
      rw [shape _ present, form] at same
      cases same
      exact ⟨rfl, _, .fault child, rfl⟩
    | singleton head =>
      exact ⟨rfl, _, .fault (ScalarStatementViews.expression_fault unique contains form head), rfl⟩

theorem discard_view {expression : ExpressionId} {semi : Bool}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression semi) (guard : (!semi && mode && rest.isEmpty) = false)
    (trace : Executes mode program context evidence source environment before (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧
      Dynamic.ExpressionFaults program context evidence source environment before expression reason after) ∨
    (∃ value middle, Dynamic.ExpressionEvaluates program context evidence source environment before expression value middle ∧
      Executes mode program context evidence source environment middle rest finalContext outcome after) := by
  cases source_view trace with
  | control executed =>
    rcases ScalarStatementViews.cons_view mode unique contains (not_tail form guard) executed with ⟨_, _, _, head, tail⟩ | ⟨head, terminal⟩
    · obtain ⟨rfl, same, value, child⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact .inr ⟨value, _, child, by cases mode <;> exact .control tail⟩
    · obtain ⟨_, rfl, _, _⟩ := ScalarStatementViews.expression unique contains form head
      cases terminal
  | fault failed =>
    rcases ScalarStatementViews.cons_fault_view mode unique contains (not_tail form guard) failed with ⟨same, head⟩ | ⟨_, _, _, head, tail⟩
    · exact .inl ⟨_, same, rfl, ScalarStatementViews.expression_fault unique contains form head⟩
    · obtain ⟨rfl, same, value, child⟩ := ScalarStatementViews.expression unique contains form head
      cases same
      exact .inr ⟨value, _, child, by cases mode <;> exact .fault tail⟩
end Source

variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {certificate : GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  (unique : NodeOccurrencesUnique source) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (preservation : ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  (reflection : ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
    program context evidence source certificate faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)

include extension transport preservation faithful observations unique in
/-- The entire finite source sequence determines a native execution. No child
execution or universal child meaning is a certificate premise. -/
theorem Tree.preserves {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree values source context certificate scope administrative ambient.definitions mode statements expected type code)
    (errors : Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (trace : Executes mode program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction errors generalizing mapping world actual before after store ξ outcome finalContext actualContext with
  | @nil mode expected type allowed =>
    cases source_view trace with
    | control executed =>
      obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.nil_view mode executed
      exact ⟨rfl, _, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
        heaps, .refl _, .refl _, .refl _ _, .refl _⟩
    | fault failed => exact False.elim (ScalarStatementViews.nil_cannot_fault mode failed)
  | @returnUnit mode id node rest found form =>
    obtain ⟨rfl, rfl, rfl⟩ := return_unit_view unique (lookupStatement?_sound found) form trace
    exact ⟨rfl, _, store, mapping, world, LocalLoop.returned_evaluates .unit, .returned .unit,
      heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | @returnValue mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    obtain ⟨rfl, expressionOutcome, childTrace, rfl⟩ := return_value_view unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      preservation child expressionFound
        environments heaps locals agrees actualTyped installed childTrace
    cases represented with
    | value payload =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | @tail id node expression expressionNode expected lowered found form expressionFound valueType child =>
    obtain ⟨rfl, expressionOutcome, childTrace, rfl⟩ := tail_view unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
      preservation child expressionFound
        environments heaps locals agrees actualTyped installed childTrace
    cases represented with
    | value payload =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
    | fault matched =>
      exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
  | @discard mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    rcases discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        preservation child expressionFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨rfl, _, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        preservation child expressionFound
          environments heaps locals agrees actualTyped installed (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨same, value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
          ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds))
            (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata) tail
        refine ⟨same, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | @assignment mode id node assignment operator rhs rest expected type body found form head projected remaining headErrors remainingErrors ih =>
    have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
        (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
        (tail : Executes mode program middleContext evidence source next middle rest finalContext outcome after) :
        finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
          Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
          FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
          LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
          AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
      obtain ⟨rfl, same, updated, assigned⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
      cases same
      obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, frame, metadata, count, typed, observed, continuation⟩ :=
        ProtectedAssignmentStatements.Head.preserves_prefix functions extension program evidence transport preservation faithful observations
          head projected environments heaps locals agrees actualTyped installed assigned
      obtain ⟨same, value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
        ih (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed observed tail
      exact ⟨same, value, finalStore, finalMap, finalWorld,
        (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count,
          SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata⟩
    cases source_view trace with
    | control executed =>
      rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
        ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
      · exact go first (by cases mode <;> exact .control tail)
      · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
        cases terminal
    | fault failed =>
      rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
        ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
      · obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, observed⟩ :=
          ProtectedAssignmentStatements.Head.preserves_fault functions extension program evidence transport preservation faithful observations
            head projected environments heaps locals agrees actualTyped installed headErrors
            (ScalarStatementViews.assignValue_fault unique (lookupStatement?_sound found) form first) body (LocalLoop.controlType type)
        exact ⟨rfl, _, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
      · exact go first (by cases mode <;> exact .fault tail)

include extension transport reflection preservation faithful observations functionTypes in
/-- Every completed generated flow constructs its independent source trace.
The returned expression trace is derived from the actual native subtree. -/
theorem Tree.reflects {mode : Bool} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree values source context certificate scope administrative ambient.definitions mode statements expected type code)
    (errors : Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction errors generalizing mapping world actual before store finalStore ξ value actualContext with
  | @nil mode expected type allowed =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.fallthrough_evaluates type actual store)
    exact ⟨_, before, mapping, world, nil_executes mode program context evidence source environment before, .fallthrough environment, heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | @returnUnit mode id node rest found form =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated (LocalLoop.returned_evaluates (.unit : Evaluates actual store .unit .unit store))
    exact ⟨_, before, mapping, world,
      terminal_intro mode rest (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnUnit (lookupStatement?_sound found) form) (.returned _),
      .returned .unit, heaps, .refl _, .refl _, .refl _ _, .refl _⟩
  | @returnValue mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault mode rest (.returnValue (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | value payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_success _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld,
            terminal_intro mode rest (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnValue (lookupStatement?_sound found) form childTrace) (.returned _),
            .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
  | @tail id node expression expressionNode expected lowered found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, .fault (.tailExpression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | value payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalLoop.returnValue_success _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, .control (.tailExpression (lookupStatement?_sound found) form childTrace),
            .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata⟩
  | @discard mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | fault matched =>
        cases trace with
        | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete (LocalSequence.discard_failure _ childEvaluation)
          exact ⟨_, after, finalMap, finalWorld, head_fault mode rest (.expression (lookupStatement?_sound found) form failed),
            .fault matched, finalHeaps, maps, worlds, frame, metadata⟩
    | caseRight childEvaluation branch =>
      obtain ⟨childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        reflection child expressionFound
          environments heaps locals agrees actualTyped installed childEvaluation
      cases represented with
      | @value _ coreValue payload =>
        cases trace with
        | value childTrace =>
          obtain ⟨outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
            ih (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees _)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds))
              (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata)
              (by simpa only [GenericExpressionMeaning.rename_prefix] using branch)
          exact ⟨outcome, after, finalMap, finalWorld,
            prepend (lookupStatement?_sound found) (not_tail form guard) (.expression (lookupStatement?_sound found) form childTrace) tail,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata⟩



  | @assignment mode id node assignment operator rhs rest expected type body found form head projected remaining headErrors remainingErrors ih =>
    rcases ProtectedAssignmentStatements.Head.reflects functions extension program evidence transport preservation reflection faithful observations
      head projected environments heaps locals agrees actualTyped installed functionTypes headErrors evaluated with
      ⟨reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, frame, metadata, observed⟩ |
      ⟨updated, middle, written, middleMap, middleWorld, slots, trace, middleHeaps, maps, worlds, frame, metadata, count, typed, observed, continuation⟩
    · exact ⟨.fault reason, after, finalMap, finalWorld,
        head_fault mode rest (.assignValue (lookupStatement?_sound found) form trace), .fault matched,
        finalHeaps, maps, worlds, frame, metadata⟩
    · obtain ⟨outcome, after, finalMap, finalWorld, tail, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
        ih (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed observed
          (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using continuation)
      exact ⟨outcome, after, finalMap, finalWorld,
        prepend (lookupStatement?_sound found) (by intro _ _; simp [form]) (.assignValue (lookupStatement?_sound found) form trace) tail,
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, frame.trans lastFrame, metadata.trans lastMetadata⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedAssignmentTails

namespace Solcore.SourceSemantics.CoreLowering.NamedAssignmentStatementTail
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open TypedScopedStatements

abbrev Tree {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context) :=
  ProtectedAssignmentTails.Tree values source context
    (NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt) scope administrative ambient.definitions

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions) (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
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

include extension faithful observations runtimeViews valid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Static named argument/body trees and the real installed entry close the
entire projected assignment and fixed-scope tail. All fault prefixes are
included; no runtime child/body meaning is an external premise. -/
theorem Tree.preserves {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies compilation fuel source context solved reasonAt scope administrative mode statements expected type code)
    (errors : ProtectedAssignmentTails.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ControlOutcome} {finalContext : SourceSemantics.Context}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : Executes mode program context evidence source environment before statements finalContext outcome after) :
    finalContext = context ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  have transport := NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix
  obtain ⟨same, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    ProtectedAssignmentTails.Tree.preserves functions extension program evidence unique transport
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
      faithful observations tree errors environments heaps locals agrees actualTyped installed trace
  exact ⟨same, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    transport.extend installed maps worlds frame metadata⟩

include extension faithful observations runtimeViews valid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Actual completed Core code supplies key, getter, RHS and tail outcomes in
source order. Installed closure payloads and frame history are retained from
the real administrative preservation receipts. -/
theorem Tree.reflects {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies compilation fuel source context solved reasonAt scope administrative mode statements expected type code)
    (errors : ProtectedAssignmentTails.Tree.Errors registry faults tree)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements context outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  have transport := NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix
  obtain ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    ProtectedAssignmentTails.Tree.reflects functions extension program evidence transport
      (NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing unique owners)
      (NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
        uninitialized missing bodyUninitialized bodyMissing)
      faithful observations runtimeViews tree errors environments heaps locals agrees actualTyped installed evaluated
  exact ⟨outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    transport.extend installed maps worlds frame metadata⟩
end Solcore.SourceSemantics.CoreLowering.NamedAssignmentStatementTail
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedLexicalStatements
/-! Concrete recursive named-call expression trees close lexical initializer,
condition, discarded and returned children at their actual source contexts.
Installed global code/captures/history are explicit entry facts. Static named
contextual-tree extraction remains separate; no runtime child meaning is an
external premise of these consumers. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLexicalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open CallableIndexedHistory
abbrev Scope := SourceCoreLocalCell.Scope
abbrev ValuesContext := SourceCoreCompatibleValues.Context

abbrev Tree {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (layouts : SourceCoreAllocationLayouts.Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  GenericLexicalStatements.Tree layouts owner active frame globals onError values source
    (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)

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

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings and condition
slots. The actual protected entry is retained as a runtime boundary. -/
theorem Tree.preserves {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      context scope mode statements expected type code) :
    ProtectedLexicalStatements.Preserves functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedLexicalStatements.Tree.preserves functions definitions registered program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    tree valid unique environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem Tree.reflects {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt
      context scope mode statements expected type code) :
    ProtectedLexicalStatements.Reflects functions program evidence
      (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world administrative actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedLexicalStatements.Tree.reflects functions definitions registered program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    tree valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

/-- Scoped restoration retains the old canonical caller environment while
transporting its actual observations through all heap/admin suffix effects. -/
theorem retained {scope : Scope} {mapping finalMap : LocationMap} {world finalWorld : StoreTyping}
    {before after : Dynamic.Heap} {store finalStore : Store} {canonical : Environment}
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
    (frame : AdministrativePreserved mapping store finalMap finalStore)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope finalMap finalWorld after finalStore canonical :=
  (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix).extend installed maps worlds frame metadata

end Solcore.SourceSemantics.CoreLowering.NamedLexicalStatements
end
