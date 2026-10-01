import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewAllocations
import Solcore.SourceSemantics.CoreLowering.GenericLexicalStatementTree
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionLiteralCertificates

/-! Static lexical body certificates survive local metadata views on a disjoint
body footprint. Expression certificates are transported at exactly the reached
child occurrences. This interface assumes no child execution or body meaning;
its concrete builtin-expression instantiation is a separate remaining step.
Real marker and snapshot receipts retain identical generated Core syntax. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
open Frontend SourceInference Core
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericLexicalStatements

/-- Transport one actual finite statement certificate. The child interface is
static and restricted to the body's reached expression occurrences. -/
theorem transport {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    (edited : LocalView source view changed) (avoids : Avoids source roots changed)
    (expressions : ∀ context scope id lowered, Reaches source roots (.expression id) →
      before context scope id lowered → after context scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source before context scope mode statements expected type code)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    Tree layouts owner active frame globals onError values view after context scope mode statements expected type code := by
  induction tree with
  | nil allowed => exact .nil allowed
  | returnUnit rest found form => exact .returnUnit rest (edited.metadata.symm.statement found) form
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType value =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .returnValue rest (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans expressionFound) valueType
      (expressions context scope expression lowered child value)
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType value =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .tail (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans expressionFound) valueType
      (expressions context scope expression lowered child value)
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocated annotation same remaining ih =>
    let allocation := CallableLambdaViewAllocations.allocation
      (request := absentRequest source scope binder payload)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := absentRequest source scope binder payload) edited.metadata annotation
    rw [← identical]
    exact .uninitialized (edited.metadata.symm.statement found) form mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary) projected allocation annotated
      (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same) (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initializerFound sourceType initial allocated annotation same remaining ih =>
    have child : Reaches source roots (.expression initializer) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    let allocation := CallableLambdaViewAllocations.allocation
      (request := initializedRequest source scope binder lowered.type)
      (CallableIndexedLambdaViewPrefix.sourceView_eq edited.metadata) allocated
    obtain ⟨annotated, original, identical⟩ := CallableLambdaViewAllocations.annotation
      (request := initializedRequest source scope binder lowered.type) edited.metadata annotation
    rw [← identical]
    exact .initialized (edited.metadata.symm.statement found) form mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (expressions context scope initializer lowered child initial) allocation annotated (by simpa only [allocation, CallableLambdaViewAllocations.allocation] using original.trans same)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @discard context scope mode id node expression expressionNode semicolon rest expected lowered type body found form notTail expressionFound value remaining ih =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .discard (edited.metadata.symm.statement found) form notTail
      ((expression_lookup edited avoids child).symm.trans expressionFound)
      (expressions context scope expression lowered child value)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH restIH =>
    exact .block (edited.metadata.symm.statement found) form
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @ifThen context scope mode id node condition conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH restIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    exact .ifThen (edited.metadata.symm.statement found) form
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType
      (expressions context scope condition ⟨.bool, conditionCode⟩ child conditionTree)
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))

/-- The body list itself supplies every statement root. -/
theorem body {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {changed : List ExpressionId}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (edited : LocalView source view changed) (avoids : Avoids source (statements.map NodeId.statement) changed)
    (expressions : ∀ context scope id lowered, Reaches source (statements.map NodeId.statement) (.expression id) →
      before context scope id lowered → after context scope id lowered)
    (tree : Tree layouts owner active frame globals onError values source before context scope mode statements expected type code) :
    Tree layouts owner active frame globals onError values view after context scope mode statements expected type code :=
  transport edited avoids expressions tree (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))


/-- Recover the canonical body's static Tree from a compiler-view Tree.
Freshness is stated on the canonical body; the metadata topology theorem
transports it back to the actual view without assuming a tree-shaped graph. -/
theorem original {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {changed : List ExpressionId}
    {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (edited : LocalView source view changed) (avoids : Avoids source (statements.map NodeId.statement) changed)
    (expressions : ∀ context scope id lowered, Reaches source (statements.map NodeId.statement) (.expression id) →
      before context scope id lowered → after context scope id lowered)
    (tree : Tree layouts owner active frame globals onError values view before context scope mode statements expected type code) :
    Tree layouts owner active frame globals onError values source after context scope mode statements expected type code := by
  have reversed : LocalView view source changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  exact body reversed (avoids.view edited.metadata)
    (fun context scope id lowered reached => expressions context scope id lowered (reached.metadata edited.metadata.symm)) tree

/-- The literal-only instance closes the static child transformation using
complete lookup equality; even resolved numerals retain their evidence IDs.
The full recursive builtin expression instance is not asserted here. -/
theorem literals {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {changed : List ExpressionId}
    {solved : List SolvedRequirement} {context : SourceSemantics.Context} {scope : Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (edited : LocalView source view changed) (avoids : Avoids source (statements.map NodeId.statement) changed)
    (tree : Tree layouts owner active frame globals onError values source
      (fun _ _ => CompatibleExpressionLiterals.Certificate solved source)
      context scope mode statements expected type code) :
    Tree layouts owner active frame globals onError values view
      (fun _ _ => CompatibleExpressionLiterals.Certificate solved view)
      context scope mode statements expected type code := by
  apply body edited avoids ?_ tree
  intro context scope id lowered reached certificate
  obtain ⟨node, found, literal⟩ := certificate
  exact ⟨node, (expression_lookup edited avoids reached).symm.trans found, literal⟩

/-- A literal body extracted at the actual compiler view recovers the
canonical static certificate without equating the complete source records. -/
theorem literals_original {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
    {values : ValuesContext} {source view : TypedSource} {changed : List ExpressionId}
    {solved : List SolvedRequirement} {context : SourceSemantics.Context} {scope : Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (edited : LocalView source view changed) (avoids : Avoids source (statements.map NodeId.statement) changed)
    (tree : Tree layouts owner active frame globals onError values view
      (fun _ _ => CompatibleExpressionLiterals.Certificate solved view)
      context scope mode statements expected type code) :
    Tree layouts owner active frame globals onError values source
      (fun _ _ => CompatibleExpressionLiterals.Certificate solved source)
      context scope mode statements expected type code := by
  apply original edited avoids ?_ tree
  intro context scope id lowered reached certificate
  obtain ⟨node, found, literal⟩ := certificate
  exact ⟨node, (expression_lookup edited avoids reached).trans found, literal⟩

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewBodyTree
