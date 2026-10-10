import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeAssignmentChildren
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree

/-! Actual native typing is pulled back through the literal one-level compiler
head. Child certificates retain that same local witness. Source metadata stays
in the original head; no Source authority or execution is inferred from typing.
The separate open call slot must supply its own authentic emission inversion.
This is a static strengthening used by the finite compiler skeleton fold. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedExpressionNativeChildren
open Core Frontend SourceInference
open CompatibleExpressionPrimitives
open CallableIndexedOwnedPreparedNativeAssignmentChildren (RawTyped packed_children)
open TypedLexicalWhile.Native (remove_front)

/-- Retain the original child receipt and its actual arbitrary native result. -/
def WithRaw (nativeContext : Core.Context) (definitions : DataEnvironment)
    (children : GenericExpressionMeaning.Certificate) : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => children scope id lowered ∧ RawTyped nativeContext lowered.expression definitions

variable {definitions : DataEnvironment} {nativeContext : Core.Context} {nativeType : Ty}

/-- Ordinary language-result operand insertion is removed syntactically. -/
theorem pair_children {leftType rightType : Ty} {left right : Expr}
    (typed : HasType nativeContext (LocalSequence.pair leftType rightType left right) nativeType definitions) :
    RawTyped nativeContext left definitions ∧ RawTyped nativeContext right definitions := by
  cases typed with
  | caseE first failure remaining =>
    cases remaining with
    | caseE second failure returned => exact ⟨⟨_, first⟩, ⟨_, remove_front second⟩⟩

/-- This also covers comparison bodies: only the two operand positions matter. -/
theorem binary_children {result : Ty} {left right body : Expr}
    (typed : HasType nativeContext (LocalPrimitiveResults.binaryWith result left right body) nativeType definitions) :
    RawTyped nativeContext left definitions ∧ RawTyped nativeContext right definitions := by
  cases typed with
  | caseE first failure remaining =>
    cases remaining with
    | caseE second failure returned => exact ⟨⟨_, first⟩, ⟨_, remove_front second⟩⟩

/-- Native branch typing exists for both branches, independently of which
branch a later actual evaluation takes. No branch evaluation is supplied. -/
theorem choose_children {result : Ty} {condition yes no : Expr}
    (typed : HasType nativeContext (LocalControl.choose result condition yes no) nativeType definitions) :
    RawTyped nativeContext condition definitions ∧ RawTyped nativeContext yes definitions ∧
      RawTyped nativeContext no definitions := by
  cases typed with
  | caseE condition failure selected =>
    cases selected with
    | ifE test yes no => exact ⟨⟨_, condition⟩, ⟨_, remove_front yes⟩, ⟨_, remove_front no⟩⟩

/-- The actual scalar profile decides strict or Boolean code shape. Short
circuiting changes evaluation, but both real child syntax typings remain. -/
theorem profiled_binary_children {operator : Syntax.BinaryOp} {operand result : TypeSystem.Ty}
    {mode : Mode} {left right : Expr}
    (profile : BinaryProfile operator operand result mode)
    (typed : HasType nativeContext (mode.binary operator left right) nativeType definitions) :
    RawTyped nativeContext left definitions ∧ RawTyped nativeContext right definitions := by
  cases profile with
  | word strict =>
    rw [Mode.binary_strict .word strict] at typed
    exact binary_children typed
  | integer strict =>
    rw [Mode.binary_strict .integer strict] at typed
    exact binary_children typed
  | logicalAnd =>
    have children := choose_children (show HasType nativeContext
      (LocalControl.choose .bool left right (LanguageResult.success (.bool false))) nativeType definitions from typed)
    exact ⟨children.1, children.2.1⟩
  | logicalOr =>
    have children := choose_children (show HasType nativeContext
      (LocalControl.choose .bool left (LanguageResult.success (.bool true)) right) nativeType definitions from typed)
    exact ⟨children.1, children.2.2⟩

/-- Actual contracted invocation contains the callee once and the packed
arguments after its two private inserted payloads. Gates supply no authority. -/
theorem contracted_call_children {gates : List CallableContract.Gate} {unknown : Word}
    {result : Ty} {callee arguments : Expr}
    (typed : HasType nativeContext (CallableContract.call gates unknown result callee arguments) nativeType definitions) :
    RawTyped nativeContext callee definitions ∧ RawTyped nativeContext arguments definitions := by
  cases typed with
  | caseE callee failure beforeArguments =>
    cases beforeArguments with
    | caseE firstGate failure arguments =>
      cases arguments with
      | caseE packed failure afterArguments =>
        exact ⟨⟨_, callee⟩, ⟨_, remove_front (remove_front packed)⟩⟩

/-- The tagged helper has one private callee slot. -/
theorem tagged_call_children {result : Ty} {callee arguments : Expr}
    (typed : HasType nativeContext (TaggedFunction.call result callee arguments) nativeType definitions) :
    RawTyped nativeContext callee definitions ∧ RawTyped nativeContext arguments definitions := by
  cases typed with
  | caseE callee failure arguments =>
    cases arguments with
    | caseE packed failure applied => exact ⟨⟨_, callee⟩, ⟨_, remove_front packed⟩⟩

/-- The real direct named helper evaluates its pack before the global cell. -/
theorem named_call_arguments {signature : SourceCoreCalls.Signature} {index : Nat}
    {arguments : Expr} {internalReason : Word}
    (typed : HasType nativeContext (SourceCoreCalls.call signature index arguments internalReason) nativeType definitions) :
    RawTyped nativeContext arguments definitions := by
  cases typed with
  | caseE arguments failure applied => exact ⟨_, arguments⟩

section Strengthen
variable {children : GenericExpressionMeaning.Certificate} {source : TypedSource}
  {scope : SourceCoreLocalCell.Scope}

/-- Original order, duplicates and Source lookup receipts are preserved. -/
theorem sequence_with_raw {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (sequence : DataExpressionSequence.Tree source children scope ids types codes)
    (raw : ∀ code, code ∈ codes → RawTyped nativeContext code.expression definitions) :
    DataExpressionSequence.Tree source (WithRaw nativeContext definitions children) scope ids types codes := by
  revert raw
  induction sequence with
  | nil => intro raw; exact .nil
  | single found generated =>
    intro raw
    exact .single found ⟨generated, raw _ (by simp)⟩
  | cons found generated tail ih =>
    intro raw
    exact .cons found ⟨generated, raw _ (by simp)⟩ (ih (fun code member => raw code (List.mem_cons_of_mem _ member)))

/-- Every actual primitive child gets its witness from the same emitted code. -/
theorem primitive_with_raw {checked : SourceCoreCompatibleCatalog.Checked}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : CompatibleExpressionTypedCompositions.Head checked source children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    CompatibleExpressionTypedCompositions.Head checked source (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | group metadata form found sourceType child =>
    exact .group metadata form found sourceType ⟨child, _, typed⟩
  | pair metadata form firstFound secondFound sourceType first second =>
    have native := pair_children typed
    exact .pair metadata form firstFound secondFound sourceType ⟨first, native.1⟩ ⟨second, native.2⟩
  | unary metadata form found inputType outputType profile child =>
    cases typed with
    | caseE operand failure returned =>
      exact .unary metadata form found inputType outputType profile ⟨child, _, operand⟩
  | binary metadata form firstFound secondFound firstType secondType outputType profile first second =>
    have native := profiled_binary_children profile typed
    exact .binary metadata form firstFound secondFound firstType secondType outputType profile
      ⟨first, native.1⟩ ⟨second, native.2⟩
  | conditional metadata form conditionFound yesFound noFound conditionType yesType noType condition yes no =>
    have native := choose_children typed
    exact .conditional metadata form conditionFound yesFound noFound conditionType yesType noType
      ⟨condition, native.1⟩ ⟨yes, native.2.1⟩ ⟨no, native.2.2⟩

/-- Builtin arguments keep the original pack and every actual child receipt. -/
theorem builtin_with_raw {values : SourceCoreCompatibleValues.Context}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : BuiltinCalls.Typed.Head values source children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    BuiltinCalls.Typed.Head values source (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | contracted metadata form sourceType sequence nativeTypes =>
    obtain ⟨_, pack⟩ := contracted_call_children typed
    obtain ⟨packType, packTyped⟩ := pack
    exact .contracted metadata form sourceType (sequence_with_raw sequence (packed_children packTyped)) nativeTypes

/-- The open call head is strengthened by its authentic one-level code
inversion. This is a static compiler operation, not an expression meaning law. -/
theorem head_with_raw {values : SourceCoreCompatibleValues.Context} {context : SourceSemantics.Context}
    {reasonAt : ExpressionId → Word}
    {calls : GenericExpressionMeaning.Certificate → GenericExpressionMeaning.Certificate}
    (callChildren : ∀ {id lowered}, calls children scope id lowered →
      ∀ {result}, HasType nativeContext lowered.expression result definitions →
        calls (WithRaw nativeContext definitions children) scope id lowered)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : CompatibleExpressionCalls.Head calls values source context reasonAt children scope id lowered)
    (typed : HasType nativeContext lowered.expression nativeType definitions) :
    CompatibleExpressionCalls.Head calls values source context reasonAt
      (WithRaw nativeContext definitions children) scope id lowered := by
  cases head with
  | primitive head => exact .primitive (primitive_with_raw head typed)
  | constructor receipt form valid sequence =>
    cases typed with
    | caseE pack failure constructed =>
      exact .constructor receipt form valid (sequence_with_raw sequence (packed_children pack))
  | member metadata baseMetadata form layout child =>
    cases typed with
    | caseE base failure projected =>
      exact .member metadata baseMetadata form layout ⟨child, _, base⟩
  | index header keyFound form sourceType base key =>
    cases typed with
    | caseE baseTyped failure remaining =>
      cases remaining with
      | caseE keyTyped failure lookup =>
        exact .index header keyFound form sourceType ⟨base, _, baseTyped⟩ ⟨key, _, remove_front keyTyped⟩
  | builtin head => exact .builtin (builtin_with_raw head typed)
  | call head => exact .call (callChildren head typed)
  | tuple receipt sequence =>
    exact .tuple receipt (sequence_with_raw sequence (packed_children typed))

end Strengthen
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedExpressionNativeChildren
