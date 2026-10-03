import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCertificateNativeTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts

/-! The same call Tree types ordinary expressions and direct named calls.
Only authenticated global reference positions are required from the caller.
Callee executions, cached body meaning and runtime result typing are absent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionScalarNativeTyping CompatibleExpressionConstructorNativeTyping
open CompatibleExpressionMemberNativeTyping CompatibleExpressionDataLeafNativeTyping
open CompatibleExpressionCertificateNativeTyping CompatibleCatalogNominalCoverage
open CallableAncestryPairedLookup RecursiveNamedCatalog

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

/-- Positions are relative to the administrative suffix after source locals.
Only members of this exact inventory can occur in a named call head. -/
def Slots (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (administrative : Core.Context) : Prop :=
  ∀ header, header ∈ headers →
    administrative[compilation.administrativePrefix + header.slot]? = some header.named.signature.referenceType

private theorem primitive_native {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {children : GenericExpressionMeaning.Certificate} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {context : Core.Context}
    (head : CompatibleExpressionTypedCompositions.Head values.checked source children scope id lowered)
    (typed : ∀ child code, children scope child code → NativeTyping values.checked.catalog.definitions context code) :
    NativeTyping values.checked.catalog.definitions context lowered := by
  cases head with
  | group _ _ _ _ child => exact typed _ _ child
  | pair _ _ _ _ _ first second =>
    have a := typed _ _ first
    have b := typed _ _ second
    exact ⟨.product a.1 b.1, LocalSequence.pair_hasType a.1 b.1 a.2 b.2⟩
  | unary _ _ _ _ _ profile child =>
    have operand := typed _ _ child
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType operand.2⟩
  | binary _ _ _ _ _ _ _ _ first second => exact binary_native (typed _ _ first).2 (typed _ _ second).2
  | conditional _ _ _ _ _ _ _ _ first second third =>
    have a := typed _ _ first
    have b := typed _ _ second
    have c := typed _ _ third
    exact ⟨b.1, LocalControl.choose_hasType b.1 a.2 b.2 c.2⟩

theorem named_native {source : TypedSource} {sourceContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {children : GenericExpressionMeaning.Certificate}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {administrative : Core.Context}
    (slots : Slots headers compilation administrative)
    (head : RecursiveNamedCatalog.Head headers compilation source sourceContext children scope id lowered)
    (typed : ∀ child code, children scope child code →
      NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) code) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  RecursiveNamedCallEvidenceHeads.native (evidence := []) slots (.ordinary head) typed

variable {readFuel : Nat} {source : TypedSource} {context : SourceSemantics.Context}
  {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
  {administrative : Core.Context} (slots : Slots headers compilation administrative)

include shaped complete slots in
theorem tree_native_with (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (tree : CompatibleExpressionCalls.Tree (RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context) readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact builtins_native administrative shaped complete child
  | node head _ ih =>
    have children := fun child code (receipt : CompatibleExpressionCalls.Entries scope _ scope child code) =>
      ih child code receipt.2
    cases head with
    | primitive head => exact primitive_native head children
    | constructor receipt _ _ sequence =>
      have packed := packed_native sequence children
      have registered := receipt.registered
      rw [← packed_type] at registered
      obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
      exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType _ registered packed.2⟩
    | member _ baseMetadata _ layout child =>
      have childType := child_type layout baseMetadata.projected
      exact ⟨result_wellFormed layout, layout_native layout shaped complete
        (by rw [← childType]; exact (children _ _ child).2)⟩
    | index header _ _ _ first second => exact index_native header (children _ _ first) (children _ _ second) (reasonAt _)
    | builtin head => exact BuiltinCallNativeTyping.Head.native head children
    | call head =>
      cases callerEvidence with
      | none => exact named_native slots head children
      | some evidence => exact RecursiveNamedCallEvidenceHeads.native slots head children
    | tuple _ sequence => exact packed_native sequence children

include shaped complete slots in
theorem tree_native
    (tree : Expressions headers compilation readFuel source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered :=
  tree_native_with shaped complete slots none tree

include shaped complete slots in
theorem tree_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : Expressions headers compilation readFuel source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, typed⟩ := tree_native shaped complete slots tree
  exact ⟨wellFormed.extend_definitions extension, typed.extend_definitions extension⟩

include shaped complete slots in
/-- Expression support follows the same native derivation in the exact
source/global context. This does not prove support for an entire cached body,
whose parameter, allocator, loop and frame wrappers need separate inversion. -/
theorem tree_supported
    (tree : Expressions headers compilation readFuel source context solved reasonAt scope id lowered) :
    NativeExpressionContextSupport.supported lowered.expression (scope.length + administrative.length) = true := by
  simpa only [List.length_append, SourceCoreLocalCell.coreContext, List.length_map] using
    NativeExpressionContextSupport.of_typing (tree_native shaped complete slots tree).2

include shaped complete slots in
theorem tree_native_with_at (callerEvidence : Option Dynamic.EvidenceEnvironment) {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionCalls.Tree (RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context)
      readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, typed⟩ := tree_native_with shaped complete slots callerEvidence tree
  exact ⟨wellFormed.extend_definitions extension, typed.extend_definitions extension⟩

include shaped complete slots in
theorem tree_supported_with (callerEvidence : Option Dynamic.EvidenceEnvironment)
    (tree : CompatibleExpressionCalls.Tree (RecursiveNamedCallEvidenceHeads.Calls callerEvidence headers compilation source context)
      readFuel values source context solved reasonAt scope id lowered) :
    NativeExpressionContextSupport.supported lowered.expression (scope.length + administrative.length) = true := by
  simpa only [List.length_append, SourceCoreLocalCell.coreContext, List.length_map] using
    NativeExpressionContextSupport.of_typing (tree_native_with shaped complete slots callerEvidence tree).2

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionNativeTyping
