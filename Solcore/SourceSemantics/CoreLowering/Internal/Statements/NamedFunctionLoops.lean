import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.BuiltinBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.LoopStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericImperativeForTrees
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LambdaViewsAndMarkedCaptures
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.TypedLexicalControl

/-!
# Named function bodies with loops

Meaning and fallthrough of function bodies with `for` and `while` loops.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
/-! One concrete named expression family closes every statement child, including
loop conditions and arbitrary nested loop bodies. Installed global code, exact
captures and frame history remain independent entry facts. Projected unary assignments, match and whole contextual
extraction remain outside this grammar. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
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
    (expressionSyntax : ExpressionId → Prop) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (administrative : Core.Context) :=
  GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax
    (fun context => NamedCallExpressions.Tree bodies compilation fuel source context solved reasonAt)
    ambient.definitions administrative

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {fuel : Nat} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
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
theorem Tree.preserves_reachable [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedImperativeFor.preservesAt_for (diagnosticPolicy := .reachable) functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    faithful observations unique tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- The finite statement tree and concrete expression/body certificates close
all runtime child obligations, including after source bindings, condition slots and seven-slot writes. The actual protected entry is retained as a runtime boundary. -/
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  apply Tree.preserves_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem Tree.reflects_reachable [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.ReachableErrors registry faults tree) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedImperativeFor.reflectsAt_for (diagnosticPolicy := .reachable) functions definitions registered extension program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun context valid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    faithful observations runtimeViews unique tree errors valid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

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

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source expressionSyntax solved reasonAt administrative
      context scope (.statements mode statements) expected type code)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.NamedImperativeForStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionFallthrough
/-! Function-mode fallthrough fixes the raw result annotation in the same
recursive guarded grammar. This follows from independent source control and
static tree shape, including at arbitrary nested loop depths. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionFallthrough
open Core Frontend SourceInference
open TypedScopedStatements (Executes source_view)

def FallthroughAt (source : TypedSource) (expected : TypeSystem.Ty)
    (mode : Bool) (statements : List StatementId) : Prop :=
  ∀ {program : Program} {actualContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment}
    {environment nextEnvironment : Dynamic.Environment} {before after : Dynamic.Heap},
    ScalarStatementViews.ListExecutes mode program actualContext evidence source
      environment before statements finalContext (.fallthrough nextEnvironment) after →
    mode = false ∨ expected = .unit

variable {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
theorem lexical_fallthrough {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericLexicalStatements.Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source) : FallthroughAt source expected mode statements := by
  induction tree with
  | nil allowed => exact fun _ => allowed
  | returnUnit => exact fun _ => .inr rfl
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType value =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ other; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · obtain ⟨_, _, impossible, _⟩ := ScalarStatementViews.returnValue unique (lookupStatement?_sound found) form head
      cases impossible
    · cases terminal
  | tail found form expressionFound valueType value =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    cases executed with
    | singleton contains notTail head =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
      subst_vars
      exact False.elim (notTail _ form)
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal

  | terminalBlock exactUnique found form inner stops issued innerIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · cases GenericLexicalStatements.block_terminates exactUnique found form stops head
    · cases terminal
  | terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · cases GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops head
    · cases terminal

theorem assignment_fallthrough {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : ProtectedLexicalAssignments.Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source) : FallthroughAt source expected mode statements := by
  induction tree with
  | lexical fragment => exact lexical_fallthrough fragment unique
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head errors remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal

theorem loop_fallthrough {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : ProtectedLoopStatements.Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope mode statements expected type code)
    (unique : NodeOccurrencesUnique source) : FallthroughAt source expected mode statements := by
  induction tree with
  | lexical fragment => exact assignment_fallthrough fragment unique
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head errors remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @breaking context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, tail⟩ | ⟨_, terminal⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique (lookupStatement?_sound found) form head
      cases impossible
    · cases terminal
  | @continuing context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, tail⟩ | ⟨_, terminal⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique (lookupStatement?_sound found) form head
      cases impossible
    · cases terminal
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode code reason found form conditionFound conditionType typed loopBody nativeTyped remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view _ unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal

theorem true_fallthrough_unit {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : ProtectedLoopStatements.Tree layouts owner active frame globals onError values source expressions
      administrative definitions registry faults context scope true statements expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment}
    {environment nextEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    (trace : Executes true program actualContext evidence source environment before
      statements finalContext (.fallthrough nextEnvironment) after) : expected = .unit := by
  cases source_view trace with
  | control executed => exact (loop_fallthrough tree unique executed).resolve_left (by decide)

end Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionFallthrough
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedForFunctionFallthrough
/-! Raw Unit fallthrough follows from the actual independent source control
and the same recursive for grammar used for native preservation/reflection.
Initializer positions introduce no separate body profile or loop induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedForFunctionFallthrough
open Core Frontend SourceInference
open TypedScopedStatements (Executes source_view)

def FallthroughAt (source : TypedSource) (expected : TypeSystem.Ty) : GenericImperativeFor.Position → Prop
  | .initializers _ _ _ _ => True
  | .statements mode statements => NamedLoopFunctionFallthrough.FallthroughAt source expected mode statements

variable {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}

theorem fallthrough {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeFor.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates
      definitions administrative context scope position expected type code)
    (unique : NodeOccurrencesUnique source) : FallthroughAt source expected position := by
  induction tree with
  | body _ fragment => exact NamedLoopFunctionFallthrough.lexical_fallthrough fragment unique
  | @uninitialized context nextContext scope mode id node binder rest expected type code payload found form mono extended ordinary projected allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered code rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same tail ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type code found form guard expressionFound value remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (TypedScopedStatements.not_tail form guard) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @block context scope mode id node statements rest expected type innerCode code found form inner remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode code found form conditionFound conditionType typed thenTree elseTree remaining thenIH elseIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @breaking context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, tail⟩ | ⟨_, terminal⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique (lookupStatement?_sound found) form head
      cases impossible
    · cases terminal
  | @continuing context scope mode id node rest expected type found form =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, tail⟩ | ⟨_, terminal⟩
    · obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique (lookupStatement?_sound found) form head
      cases impossible
    · cases terminal
  | @whileLoop context scope mode id node condition conditionNode statements rest expected type conditionCode loopCode code reason found form conditionFound conditionType typed loopBody nativeTyped remaining innerIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining ih =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact ih tail
    · cases terminal
  | @forLoop context scope mode id node initializer condition post statements rest expected type initialCode body found form initial remaining initialIH restIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, _, tail⟩ | ⟨_, terminal⟩
    · exact restIH tail
    · cases terminal
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · cases GenericLexicalStatements.block_terminates exactUnique found form stops head
    · cases terminal
  | @terminalIf context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType typed thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    intro program actualContext finalContext evidence environment nextEnvironment before after executed
    rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) executed with
      ⟨_, _, _, head, _⟩ | ⟨_, terminal⟩
    · cases GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops head
    · cases terminal
  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard | initializerAssign | initializerBitNot => trivial

theorem true_fallthrough_unit {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : GenericImperativeFor.Tree layouts owner active frame globals onError values source expressionSyntax certificates
      definitions administrative context scope (.statements true statements) expected type code)
    (unique : NodeOccurrencesUnique source)
    {program : Program} {actualContext finalContext : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment}
    {environment nextEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    (trace : Executes true program actualContext evidence source environment before
      statements finalContext (.fallthrough nextEnvironment) after) : expected = .unit := by
  cases source_view trace with
  | control executed => exact (fallthrough tree unique executed).resolve_left (by decide)

end Solcore.SourceSemantics.CoreLowering.NamedForFunctionFallthrough
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedForFunctionBodyMeaning
/-! Actual accepted named function bodies with recursive lexical control,
assignment and nested while/for preserve finite source calls and reflect completed
Core calls. Concrete named trees close every runtime child obligation.
Escaped loop control retains its independent source fault. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedForFunctionBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open TypedScopedStatements (Executes source_view)
open CompatibleNamedBody (trace_control)
open ImperativeFunctionFinish (result)

structure Certificate {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (source : TypedSource) (expressionSyntax : ExpressionId → Prop) (context : SourceSemantics.Context)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (policy : SourceCoreLoops.Policy)
    (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
    statements type reasonAt fellThrough escaped = .ok code
  projection : values.checked.catalog.project expected = .ok type
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
    statements type reasonAt true escaped = .ok flow
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : NamedImperativeForStatements.Tree bodies layouts owner active frame globals onError compilation expressionFuel
    source expressionSyntax solved reasonAt administrative context scope (.statements true statements) expected type flow
  errors : GenericImperativeFor.Tree.Errors registry faults tree

/-- The chosen operand diagnostic policy is retained by the static body receipt.
The tree, emitted finish code and actual compiler equations are unchanged. -/
structure CertificateFor (diagnosticPolicy : AssignmentDiagnosticPolicy) {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (source : TypedSource) (expressionSyntax : ExpressionId → Prop) (context : SourceSemantics.Context)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (policy : SourceCoreLoops.Policy)
    (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
    statements type reasonAt fellThrough escaped = .ok code
  projection : values.checked.catalog.project expected = .ok type
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
    statements type reasonAt true escaped = .ok flow
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : NamedImperativeForStatements.Tree bodies layouts owner active frame globals onError compilation expressionFuel
    source expressionSyntax solved reasonAt administrative context scope (.statements true statements) expected type flow
  errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree

/-- Preserve the original record while exposing its unconditional policy. -/
def Certificate.to_for
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
    (certificate : Certificate bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code) :
    CertificateFor .unconditional bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code :=
  ⟨certificate.accepted, certificate.projection, certificate.flow, certificate.generated, certificate.emitted, certificate.tree, certificate.errors⟩

/-- The compatibility record has the same fields, with no additional premise. -/
def CertificateFor.to_strict
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
    (certificate : CertificateFor .unconditional bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code) :
    Certificate bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code :=
  ⟨certificate.accepted, certificate.projection, certificate.flow, certificate.generated, certificate.emitted, certificate.tree, certificate.errors⟩

def of_extracted_for {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
      statements type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project expected = .ok type)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax solved reasonAt administrative context scope (.statements true statements) expected type flow)
    (errors : GenericImperativeFor.Tree.ErrorsFor diagnosticPolicy registry faults tree) :
    CertificateFor diagnosticPolicy bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code := by
  have emitted : code = CompatibleStatements.finish type flow fellThrough escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨accepted, projection, flow, generated, emitted, tree, errors⟩

/-- Backward-compatible unconditional entry. -/
def of_extracted
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {source : TypedSource} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
      statements type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project expected = .ok type)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements type reasonAt true escaped = .ok flow)
    (tree : NamedImperativeForStatements.Tree bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax solved reasonAt administrative context scope (.statements true statements) expected type flow)
    (errors : GenericImperativeFor.Tree.Errors registry faults tree) :
    Certificate bodies layouts owner active frame globals onError compilation expressionFuel
      source expressionSyntax context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code :=
  (of_extracted_for accepted projection generated tree errors).to_strict

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {function : Dynamic.Closure} {expressionSyntax : ExpressionId → Prop} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem CertificateFor.preserves [FunctionCalls.FaultTokens faults] {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (certificate : CertificateFor diagnosticPolicy bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source expressionSyntax context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.preserves_reachable functions definitions registered extension faithful functionLeaves functionTypes function.evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing certificate.errors.reachable contextValid
      environments heaps locals agrees actualTyped reference read unmapped installed sourceTrace
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact NamedForFunctionFallthrough.true_fallthrough_unit certificate.tree unique sourceTrace)
    certificate.projection fellThrough escaped escapedFault represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [certificate.emitted, ImperativeFunctionFinish.rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, ImperativeFunctionFinish.result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩,
    NamedImperativeForStatements.retained functions installed maps worlds frame metadata⟩

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem CertificateFor.reflects [FunctionCalls.FaultTokens faults] {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (certificate : CertificateFor diagnosticPolicy bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source expressionSyntax context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  rw [certificate.emitted, ImperativeFunctionFinish.rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEval⟩ := ImperativeFunctionFinish.input evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.reflects_reachable functions definitions registered extension faithful functionLeaves functionTypes function.evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing certificate.errors.reachable contextValid
      environments heaps locals agrees actualTyped reference read unmapped installed flowEval
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact NamedForFunctionFallthrough.true_fallthrough_unit certificate.tree unique trace)
    certificate.projection fellThrough escaped escapedFault represented flowEval
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact ⟨.value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact ⟨.value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (certificate.tree.control_not_fault unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
    | breaking finalEnvironment matched =>
      cases trace with
      | control executed =>
        exact ⟨_, .escaped executed (.inl ⟨_, rfl⟩), .fault matched, .breaking _⟩
    | continuing finalEnvironment matched =>
      cases trace with
      | control executed =>
        exact ⟨_, .escaped executed (.inr ⟨_, rfl⟩), .fault matched, .continuing _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩,
    NamedImperativeForStatements.retained functions installed maps worlds frame metadata⟩


include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Finite source call completion and completed Core execution are equivalent.
Suspension is outside both sides; no common fuel bound or termination premise
is required. The stronger preceding theorems retain result and heap relations. -/
theorem CertificateFor.finite_iff [FunctionCalls.FaultTokens faults] {diagnosticPolicy : AssignmentDiagnosticPolicy}
    (certificate : CertificateFor diagnosticPolicy bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source expressionSyntax context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  constructor
  · rintro ⟨runtimeFuel, value, finalStore, completed⟩
    obtain ⟨outcome, after, _, _, trace, _⟩ :=
      certificate.reflects functions extension definitions registered
        contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
        environments heaps locals agrees actualTyped reference read unmapped installed
        (Core.runStateful_evaluation_sound completed)
    exact ⟨outcome, after, trace⟩
  · rintro ⟨outcome, after, trace⟩
    obtain ⟨value, finalStore, _, _, evaluated, _⟩ :=
      certificate.preserves functions extension definitions registered
        contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
        environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨runtimeFuel, completed⟩ :=
      Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
    exact ⟨runtimeFuel, value, finalStore, completed runtimeFuel (Nat.le_refl _)⟩
include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem Certificate.preserves [FunctionCalls.FaultTokens faults]
    (certificate : Certificate bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source expressionSyntax context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  exact certificate.to_for.preserves functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem Certificate.reflects [FunctionCalls.FaultTokens faults]
    (certificate : Certificate bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source expressionSyntax context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  exact certificate.to_for.reflects functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed evaluated

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Finite source call completion and completed Core execution are equivalent.
Suspension is outside both sides; no common fuel bound or termination premise
is required. The stronger preceding theorems retain result and heap relations. -/
theorem Certificate.finite_iff [FunctionCalls.FaultTokens faults]
    (certificate : Certificate bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source expressionSyntax context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  exact certificate.to_for.finite_iff functions extension definitions registered
    contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
    environments heaps locals agrees actualTyped reference read unmapped installed


end Solcore.SourceSemantics.CoreLowering.NamedForFunctionBody
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
/-! One concrete named expression family closes every statement child, including
loop conditions and arbitrary nested loop bodies. Installed global code, exact
captures and frame history remain independent entry facts. For, match, unary
assignment and whole contextual extraction are outside this grammar. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
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
  ProtectedLoopStatements.Tree layouts owner active frame globals onError values source
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
theorem Tree.preserves [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedWhile.Body.Preserves functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ
    contextLocation native outcome finalContext environments heaps locals agrees actualTyped reference read unmapped installed trace
  exact ProtectedLoopStatements.Tree.preserves functions definitions registered extension faithful observations program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    tree valid unique environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered extension faithful observations runtimeViews unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Every completed native lexical tree reconstructs its independent source
trace. Actual captured code/environment and frame history come from the entry,
not from native typing or the source heap relation. -/
theorem Tree.reflects [FunctionCalls.FaultTokens faults] {context : SourceSemantics.Context} {scope : Scope} {mode : Bool}
    {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree bodies layouts owner active frame globals onError compilation fuel source solved reasonAt administrative registry faults
      context scope mode statements expected type code) :
    ProtectedWhile.Body.Reflects functions program evidence
      (administrative := administrative) (entry := NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix)
      (source := source) (context := context) (registry := registry) (faults := faults)
      (solved := solved) (frameLayout := frame) (globals := globals)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ
    contextLocation native value environments heaps locals agrees actualTyped reference read unmapped installed evaluated
  exact ProtectedLoopStatements.Tree.reflects functions definitions registered extension faithful observations runtimeViews program evidence
    (NamedCallExpressions.entry_transport functions registry bodies compilation.administrativePrefix)
    (NamedCallExpressions.entry_binds functions registry bodies compilation.administrativePrefix)
    (fun context valid => NamedCallExpressions.Tree.preserves functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing unique owners)
    (fun context valid => NamedCallExpressions.Tree.reflects functions extension faithful observations runtimeViews evidence valid
      uninitialized missing bodyUninitialized bodyMissing)
    tree valid unique environments heaps locals agrees actualTyped reference read unmapped installed evaluated

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

end Solcore.SourceSemantics.CoreLowering.NamedLoopStatements
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionBodyMeaning
/-! Actual accepted named function bodies with recursive lexical control,
assignment and nested while preserve finite source calls and reflect completed
Core calls. Concrete named trees close every runtime child obligation.
Escaped loop control retains its independent source fault. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup
open TypedScopedStatements (Executes source_view)
open CompatibleNamedBody (trace_control)
open ImperativeFunctionFinish (result)

structure Certificate {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    (bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program)
    (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (compilation : SourceCoreFunctions.Context) (expressionFuel : Nat)
    (source : TypedSource) (context : SourceSemantics.Context)
    (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word)
    (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (policy : SourceCoreLoops.Policy)
    (fuel : Nat) (fellThrough escaped : Word) (code : Expr) where private mk ::
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
    statements type reasonAt fellThrough escaped = .ok code
  projection : values.checked.catalog.project expected = .ok type
  flow : Expr
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
    statements type reasonAt true escaped = .ok flow
  emitted : code = CompatibleStatements.finish type flow fellThrough escaped
  tree : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation expressionFuel
    source solved reasonAt administrative registry faults context scope true statements expected type flow

/-- Keep the real compiler equation and the exact flow traversal. Their
composition fixes the actual finish code without an additional code equality
supplied by a caller. The tree is independent static evidence. -/
def of_extracted
    {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
    {source : TypedSource} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {administrative : Core.Context}
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {policy : SourceCoreLoops.Policy}
    {fuel : Nat} {fellThrough escaped : Word} {code flow : Expr}
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
      statements type reasonAt fellThrough escaped = .ok code)
    (projection : values.checked.catalog.project expected = .ok type)
    (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements type reasonAt true escaped = .ok flow)
    (tree : NamedLoopStatements.Tree bodies layouts owner active frame globals onError compilation expressionFuel
      source solved reasonAt administrative registry faults context scope true statements expected type flow) :
    Certificate bodies layouts owner active frame globals onError compilation expressionFuel
      source context solved reasonAt administrative registry faults scope statements
      expected type policy fuel fellThrough escaped code := by
  have emitted : code = CompatibleStatements.finish type flow fellThrough escaped := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
    rw [generated] at accepted
    exact Except.ok.inj accepted.symm
  exact ⟨accepted, projection, flow, generated, emitted, tree⟩

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {bodies : NamedCallExpressions.Bodies prepared values ambient.definitions program}
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {compilation : SourceCoreFunctions.Context} {expressionFuel : Nat}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope} {type : Ty}
  {administrative : Core.Context}
  {policy : SourceCoreLoops.Policy} {fuel : Nat} {fellThrough escaped : Word} {code : Expr}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : layouts.definitions = ambient.definitions)
  (registered : frameLayout.Registered ambient.definitions)
  (contextValid : CompatibleExpressionLiterals.ContextValid solved context function.evidence)
  (unique : NodeOccurrencesUnique function.source)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup) {faults : FunctionCalls.FaultRep}
  (escapedFault : faults .controlEscapedFunction escaped)
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

  (bodyUninitialized : ∀ body, body ∈ bodies → ∀ id location,
    faults (.uninitializedLocation location) (body.reasonAt id))
  (bodyMissing : ∀ body, body ∈ bodies → ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((body.reasonAt id).add tag))

  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (functionLeaves : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem Certificate.preserves [FunctionCalls.FaultTokens faults]
    (certificate : Certificate bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (trace : FunctionCallBody.Trace program function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  obtain ⟨resultContext, control, sourceTrace, exit⟩ := trace_control trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.preserves functions definitions registered extension faithful functionLeaves functionTypes function.evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing contextValid
      environments heaps locals agrees actualTyped reference read unmapped installed sourceTrace
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact NamedLoopFunctionFallthrough.true_fallthrough_unit certificate.tree unique sourceTrace)
    certificate.projection fellThrough escaped escapedFault represented evaluated
  have evaluated : Evaluates actual store (code.rename ξ) result finalStore := by
    rw [certificate.emitted, ImperativeFunctionFinish.rename]
    exact completed
  exact ⟨result, finalStore, finalMap, finalWorld, evaluated, ImperativeFunctionFinish.result related exit,
    finalHeaps, maps, worlds, frame, metadata, ⟨resultContext, control, sourceTrace, exit, lexical⟩,
    NamedLoopStatements.retained functions installed maps worlds frame metadata⟩

include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
theorem Certificate.reflects [FunctionCalls.FaultTokens faults]
    (certificate : Certificate bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
        scope finalMap finalWorld after finalStore canonical := by
  rw [certificate.emitted, ImperativeFunctionFinish.rename] at evaluated
  obtain ⟨flowValue, middleStore, flowEval⟩ := ImperativeFunctionFinish.input evaluated
  obtain ⟨resultContext, control, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
    certificate.tree.reflects functions definitions registered extension faithful functionLeaves functionTypes function.evidence
      unique owners uninitialized missing bodyUninitialized bodyMissing contextValid
      environments heaps locals agrees actualTyped reference read unmapped installed flowEval
  obtain ⟨result, completed, related⟩ := ImperativeFunctionFinish.from_flow functions (fun next same => by
    cases same
    exact NamedLoopFunctionFallthrough.true_fallthrough_unit certificate.tree unique trace)
    certificate.projection fellThrough escaped escapedFault represented flowEval
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated completed
  have result : ∃ outcome, FunctionCallBody.Trace program function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType type faults outcome value ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
    generalize raw : function.resultType = expected at related
    cases related with
    | fallthrough finalEnvironment =>
      cases trace with
      | control executed =>
        refine ⟨_, .unit raw executed, ?_⟩
        exact ⟨.value .unit, .unit _ rfl⟩
    | returned payload =>
      cases trace with
      | control executed =>
        refine ⟨_, .returned executed, ?_⟩
        exact ⟨.value payload, .returned _⟩
    | fault matched =>
      cases trace with
      | control executed => exact False.elim (certificate.tree.control_not_fault unique executed)
      | fault failed => exact ⟨_, .fault failed, .fault matched, .fault _⟩
    | breaking finalEnvironment matched =>
      cases trace with
      | control executed =>
        exact ⟨_, .escaped executed (.inl ⟨_, rfl⟩), .fault matched, .breaking _⟩
    | continuing finalEnvironment matched =>
      cases trace with
      | control executed =>
        exact ⟨_, .escaped executed (.inr ⟨_, rfl⟩), .fault matched, .continuing _⟩
  obtain ⟨outcome, bodyTrace, result, exit⟩ := result
  exact ⟨outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps, maps, worlds, frame, metadata,
    ⟨resultContext, control, trace, exit, lexical⟩,
    NamedLoopStatements.retained functions installed maps worlds frame metadata⟩


include definitions registered escapedFault extension faithful functionLeaves functionTypes contextValid unique owners uninitialized missing bodyUninitialized bodyMissing in
/-- Finite source call completion and completed Core execution are equivalent.
Suspension is outside both sides; no common fuel bound or termination premise
is required. The stronger preceding theorems retain result and heap relations. -/
theorem Certificate.finite_iff [FunctionCalls.FaultTokens faults]
    (certificate : Certificate bodies layouts owner active frameLayout globals onError compilation expressionFuel function.source context solved reasonAt administrative registry faults scope function.body
      function.resultType type policy fuel fellThrough escaped code)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : SourceCoreCallableIndexedFrames.Frame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (unmapped : contextLocation ∉ mapping)
    (installed : NamedCallExpressions.Entry functions registry bodies compilation.administrativePrefix
      scope mapping world before store canonical)
:
    (∃ runtimeFuel value finalStore,
      Core.runStateful runtimeFuel (.initial (code.rename ξ) actual store) =
        .done value finalStore) ↔
    (∃ outcome after,
      FunctionCallBody.Trace program function context environment before outcome after) := by
  constructor
  · rintro ⟨runtimeFuel, value, finalStore, completed⟩
    obtain ⟨outcome, after, _, _, trace, _⟩ :=
      certificate.reflects functions extension definitions registered
        contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
        environments heaps locals agrees actualTyped reference read unmapped installed
        (Core.runStateful_evaluation_sound completed)
    exact ⟨outcome, after, trace⟩
  · rintro ⟨outcome, after, trace⟩
    obtain ⟨value, finalStore, _, _, evaluated, _⟩ :=
      certificate.preserves functions extension definitions registered
        contextValid unique owners escapedFault uninitialized missing bodyUninitialized bodyMissing faithful functionLeaves functionTypes
        environments heaps locals agrees actualTyped reference read unmapped installed trace
    obtain ⟨runtimeFuel, completed⟩ :=
      Core.evaluation_runStateful_complete_with_sufficient_fuel evaluated
    exact ⟨runtimeFuel, value, finalStore, completed runtimeFuel (Nat.le_refl _)⟩

end Solcore.SourceSemantics.CoreLowering.NamedLoopFunctionBody
end
