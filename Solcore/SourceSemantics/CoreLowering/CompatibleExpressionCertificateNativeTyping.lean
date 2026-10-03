import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionBuiltinNativeTyping

/-! Native expression typing follows the actual projection and read receipts.
Only referenced cells need valid annotations. Unused local scope entries are
unconstrained. Nominal identities are authenticated by the catalog lookup;
constructor payload typing continues to use its registered definitions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCertificateNativeTyping
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionScalarNativeTyping CompatibleExpressionConstructorNativeTyping
open CompatibleExpressionMemberNativeTyping CompatibleExpressionDataLeafNativeTyping
open CompatibleCatalogNominalCoverage

private theorem identity_wellFormed {catalog : SourceCoreCompatibleCatalog.Catalog}
    {sourceType : TypeSystem.Ty} {identity : DataTypeId}
    (found : catalog.identity? sourceType = some identity) :
    Ty.WellFormed catalog.definitions (.namedData identity) := by
  obtain ⟨entry, stored, _⟩ := identity_entry found
  apply Ty.WellFormed.namedData (definition := entry.definition.getD ⟨[]⟩)
  simp [SourceCoreCompatibleCatalog.Catalog.definitions, List.getElem?_map, stored]

/-- The output IDs of this projection come from actual catalog entries.
This proves the native annotation, not source authority or payload semantics. -/
theorem project_wellFormed {catalog : SourceCoreCompatibleCatalog.Catalog}
    {sourceType : TypeSystem.Ty} {type : Ty}
    (projected : catalog.project sourceType = .ok type) : type.WellFormed catalog.definitions := by
  induction sourceType generalizing type with
  | product left right first second =>
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    obtain ⟨a, leftEq, rest⟩ := CompatibleEncoding.bind_ok projected
    obtain ⟨b, rightEq, result⟩ := CompatibleEncoding.bind_ok rest
    cases result
    exact .product (first leftEq) (second rightEq)
  | function parameter result first second =>
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    obtain ⟨a, firstEq, rest⟩ := CompatibleEncoding.bind_ok projected
    obtain ⟨b, secondEq, result⟩ := CompatibleEncoding.bind_ok rest
    cases result
    unfold SourceCoreCompatibleCatalog.Catalog.functionType
    split
    · exact CallableContract.functionType_wellFormed (first firstEq) (second secondEq)
    · exact TaggedFunction.functionType_wellFormed (first firstEq) (second secondEq)
  | mapping key value first second =>
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    cases found : catalog.identity? (.mapping key value) with
    | none => simp [found, bind, Except.bind] at projected
    | some identity =>
      simp only [found, bind, Except.bind, pure, Except.pure] at projected
      obtain ⟨a, firstEq, rest⟩ := CompatibleEncoding.bind_ok projected
      obtain ⟨b, secondEq, result⟩ := CompatibleEncoding.bind_ok rest
      cases result
      exact .product .word (.product (.sum .unit (second secondEq)) (identity_wellFormed found))
  | comptime inner ih => exact ih projected
  | constructor constructor =>
    cases constructor with
    | builtin builtin => cases builtin <;> cases projected <;> constructor
    | declaration declaration =>
      simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
      cases found : catalog.identity? (.constructor (.declaration declaration)) <;> simp [found] at projected
      cases projected
      exact identity_wellFormed found
  | «variable» variableId | «parameter» parameterId | application left right _ _ | proxy inner _ | error =>
    simp only [SourceCoreCompatibleCatalog.Catalog.project] at projected
    split at projected
    · cases projected; exact identity_wellFormed (by assumption)
    · cases projected

theorem read_native {fuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (read : CompatibleExpressionReads.LoweredRead fuel values source context reasonAt scope id lowered)
    (administrative : Core.Context) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨certificate, same, binding⟩ := read
  have wellFormed := project_wellFormed certificate.metadata.projected
  exact ⟨same ▸ wellFormed, by rw [← same]; exact certificate.native_hasType binding wellFormed administrative⟩

theorem binary_native {definitions : DataEnvironment} {context : Core.Context}
    {mode : Mode} {operator : Syntax.BinaryOp} {left right : Expr}
    (first : HasType context left (LanguageResult.resultType (mode.operandType operator)) definitions)
    (second : HasType context right (LanguageResult.resultType (mode.operandType operator)) definitions) :
    NativeTyping definitions context ⟨mode.resultType operator, mode.binary operator left right⟩ := by
  constructor
  · cases mode <;> cases operator <;> constructor
  · cases mode with
    | word => exact SourceCorePrimitive.binary_hasType first second
    | integer => exact SourceCoreInteger.binary_hasType first second

theorem constructor_native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {instantiation : DataConstructorInstantiation} {ids : List ExpressionId}
    {tag : ConstructorId} {header : Word} {codes : List SourceCoreBasic.LoweredExpr} {context : Core.Context}
    (receipt : CompatibleExpressionConstructors.Header values source id node instantiation tag header codes)
    (count : ids.length = instantiation.payloadTypes.length)
    (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
    (children : ∀ child code, (child, code) ∈ ids.zip codes →
      NativeTyping values.checked.catalog.definitions context code) :
    NativeTyping values.checked.catalog.definitions context
      ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag header (SourceCoreCalls.packArguments codes).expression⟩ := by
  have sequence := CompatibleExpressionConstructors.sequence_of_nodes
    (scope := scope) (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions context code)
    count nodes children
  obtain ⟨_, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
  have registered := receipt.registered
  rw [← packed_type codes] at registered
  obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
  exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

variable {fuel readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (administrative : Core.Context)

theorem products_native
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | literal receipt =>
    obtain ⟨_, _, literal⟩ := receipt
    exact literal_native literal _ _
  | read receipt => exact read_native receipt administrative
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩

theorem primitives_native
    (tree : CompatibleExpressionPrimitives.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | product child => exact products_native administrative child
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2

theorem conditionals_native
    (tree : CompatibleExpressionConditionals.Tree fuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | primitive child => exact primitives_native administrative child
  | group _ _ _ _ _ ih => exact ih
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩

theorem constructors_native
    (tree : CompatibleExpressionConstructors.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact conditionals_native administrative child
  | @constructor id node instantiation ids tag header codes receipt form valid count nodes children ih =>
    have sequence := CompatibleExpressionConstructors.sequence_of_nodes
      (scope := scope)
      (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) count nodes ih
    obtain ⟨packedWF, packedTyped⟩ := packed_native sequence (fun _ _ typed => typed)
    have registered := receipt.registered
    rw [← packed_type codes] at registered
    obtain ⟨_, ownerRegistered⟩ := DataEnvironment.lookupConstructorPayloadType?_owner registered
    exact ⟨.namedData ownerRegistered, SourceCoreCompatibleDataExpressions.construct_hasType header registered packedTyped⟩

variable (shaped : Shapes values.checked.signatures values.checked.catalog) (complete : Complete values.checked.catalog)
include shaped complete in
theorem members_native
    (tree : CompatibleExpressionMembers.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact constructors_native administrative child
  | member metadata baseMetadata form layout childTree ih =>
    have childType := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← childType]; exact ih.2)⟩

include shaped complete in
theorem recursive_native
    (tree : CompatibleExpressionRecursive.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | fragment child => exact members_native administrative shaped complete child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩

include shaped complete in
theorem general_native
    (tree : CompatibleExpressionGeneral.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | proxy receipt => exact proxy_native receipt _
  | fragment child => exact recursive_native administrative shaped complete child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩
  | index header _ _ _ _ _ first second => exact index_native header first second (reasonAt _)

include shaped complete in
theorem builtins_native
    (tree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping values.checked.catalog.definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  induction tree with
  | proxy receipt => exact proxy_native receipt _
  | fragment child => exact general_native administrative shaped complete child
  | group _ _ _ _ _ child => exact child
  | pair _ _ _ _ _ _ _ first second =>
    exact ⟨.product first.1 second.1, LocalSequence.pair_hasType first.1 second.1 first.2 second.2⟩
  | unary _ _ _ _ _ profile _ child =>
    cases profile <;> exact ⟨by constructor, LocalPrimitiveResults.unary_hasType child.2⟩
  | binary _ _ _ _ _ _ _ _ _ _ first second => exact binary_native first.2 second.2
  | conditional _ _ _ _ _ _ _ _ _ _ _ condition yes no =>
    exact ⟨yes.1, LocalControl.choose_hasType yes.1 condition.2 yes.2 no.2⟩
  | constructor receipt _ _ count nodes _ children => exact constructor_native (scope := scope) receipt count nodes children
  | member _ baseMetadata _ layout _ child =>
    have same := child_type layout baseMetadata.projected
    exact ⟨result_wellFormed layout, layout_native layout shaped complete (by rw [← same]; exact child.2)⟩
  | index header _ _ _ _ _ first second => exact index_native header first second (reasonAt _)

  | @builtin id callee arguments function node codes identity contract unknown _ _ _ count nodes nativeTypes _ children =>
    have sequence := CompatibleExpressionConstructors.sequence_of_nodes
      (scope := scope) (certificate := fun _ _ code => NativeTyping values.checked.catalog.definitions
        (SourceCoreLocalCell.coreContext scope ++ administrative) code) count nodes children
    apply BuiltinCallNativeTyping.call_native function identity contract unknown
      (packed_native sequence (fun _ _ typed => typed))
    rw [packed_type, nativeTypes, CompatibleBuiltinMeaning.argumentTypes_pack]

include shaped complete in
theorem builtins_native_at {definitions : DataEnvironment}
    (extension : values.checked.catalog.definitions.Extends definitions)
    (tree : CompatibleExpressionBuiltins.Tree readFuel values source context solved reasonAt scope id lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  obtain ⟨wellFormed, native⟩ := builtins_native administrative shaped complete tree
  exact ⟨wellFormed.extend_definitions extension, native.extend_definitions extension⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCertificateNativeTyping
