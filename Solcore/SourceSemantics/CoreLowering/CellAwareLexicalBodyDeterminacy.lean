import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion

/-! Finite lexical completion determines every Source trace of the same body.
Each expression fact is supplied by its actual completion; allocations and
scoped control retain the exact reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}

abbrev Expression (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (id : ExpressionId) (outcome : Outcome) (after : Dynamic.Heap) : Prop :=
  ∀ {size otherOutcome otherHeap}, Size.Expression program registry size invocation context environment before id otherOutcome otherHeap →
    otherOutcome = outcome ∧ otherHeap = after

abbrev Body (mode : Bool) (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId) (finalContext : SourceSemantics.Context)
    (outcome : BodyOutcome) (after : Dynamic.Heap) : Prop :=
  ∀ {size otherContext otherOutcome otherHeap},
    Size.StatementsIn program registry mode size invocation context environment before statements otherContext otherOutcome otherHeap →
    otherContext = finalContext ∧ otherOutcome = outcome ∧ otherHeap = after

variable (unique : NodeOccurrencesUnique invocation.source)

 theorem nil {mode context environment before} :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before [] context (.fallthrough environment) before := by
  intro _ _ _ _ trace
  cases trace
  exact ⟨rfl,rfl,rfl⟩

include unique in
theorem returnUnit {mode context environment before id node rest}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id :: rest) context (.returned .unit) before := by
  intro _ _ _ _ trace
  exact CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.return_unit unique found form trace

include unique in
theorem terminal {mode context environment before expression statements outcome after}
    (head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode statements)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before expression outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before statements context
      (CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.control outcome) after := by
  intro _ _ _ _ trace
  obtain ⟨_,_,_,sameContext,sameOutcome,actual⟩ := CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion.child_of_body unique head trace
  obtain ⟨same,heap⟩ := child actual
  exact ⟨sameContext, sameOutcome.trans (congrArg _ same),heap⟩

private theorem allocation_unique {before : Dynamic.Heap} {type : TypeSystem.Ty} {value : Option Dynamic.Value}
    {first second : Dynamic.Location} {left right : Dynamic.Heap}
    (one : Dynamic.Heap.Allocates before type value first left)
    (two : Dynamic.Heap.Allocates before type value second right) : second = first ∧ right = left := by
  cases one
  cases two
  exact ⟨rfl,rfl⟩

include unique in
theorem absent {mode context nextContext environment before id node binder rest location bound finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder none)
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode nextContext
      ((binder.id,location)::environment) bound rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  obtain ⟨_,_,_,_,actualAllocation,remaining⟩ := CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.absent unique found form extended trace
  obtain ⟨rfl,rfl⟩ := allocation_unique allocated actualAllocation
  exact tail remaining

include unique in
theorem initializedFault {mode context nextContext environment before id node binder initializer rest failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before initializer (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized unique found form mono extended trace with first | second
  · obtain ⟨_,_,_,sameContext,sameOutcome,actual⟩ := first
    obtain ⟨same,heap⟩ := child actual
    cases same
    exact ⟨sameContext,sameOutcome,heap⟩
  · obtain ⟨_,_,_,_,_,_,_,actual,_,_⟩ := second
    cases (child actual).1

include unique in
theorem initialized {mode context nextContext environment before id node binder initializer rest sourceValue middle location bound finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .letDecl binder (some initializer))
    (mono : binder.scheme.quantified = []) (extended : BinderExtends invocation.source.owner context binder nextContext)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before initializer (.value sourceValue) middle)
    (allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some sourceValue) location bound)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode nextContext
      ((binder.id,location)::environment) bound rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized unique found form mono extended trace with first | second
  · obtain ⟨_,_,_,_,_,actual⟩ := first
    cases (child actual).1
  · obtain ⟨_,_,_,_,_,_,_,actual,actualAllocation,remaining⟩ := second
    obtain ⟨same,rfl⟩ := child actual
    cases same
    obtain ⟨rfl,rfl⟩ := allocation_unique allocated actualAllocation
    exact tail remaining

include unique in
theorem discardFault {mode semicolon context environment before id node expression rest failure after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
    (continuing : semicolon = true ∨ mode = false)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before expression (.fault failure) after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) context (.fault failure) after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion.child_and_tail unique (lookupStatement?_sound found) form continuing trace with first | second
  · obtain ⟨_,_,_,sameContext,sameOutcome,actual⟩ := first
    obtain ⟨same,heap⟩ := child actual
    cases same
    exact ⟨sameContext,sameOutcome,heap⟩
  · obtain ⟨_,_,_,_,_,actual,_⟩ := second
    cases (child actual).1

include unique in
theorem discard {mode semicolon context environment before id node expression rest sourceValue middle finalContext outcome after}
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .expression expression semicolon)
    (continuing : semicolon = true ∨ mode = false)
    (child : Expression (program := program) (registry := registry) (invocation := invocation) context environment before expression (.value sourceValue) middle)
    (tail : Body (program := program) (registry := registry) (invocation := invocation) mode context environment middle rest finalContext outcome after) :
    Body (program := program) (registry := registry) (invocation := invocation) mode context environment before (id::rest) finalContext outcome after := by
  intro _ _ _ _ trace
  rcases CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion.child_and_tail unique (lookupStatement?_sound found) form continuing trace with first | second
  · obtain ⟨_,_,_,_,_,actual⟩ := first
    cases (child actual).1
  · obtain ⟨_,_,_,_,_,actual,remaining⟩ := second
    obtain ⟨_,rfl⟩ := child actual
    exact tail remaining

end Solcore.SourceSemantics.CoreLowering.CellAwareLexicalBodyDeterminacy
