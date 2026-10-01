import Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeArms
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchHiddenPrefix

/-! One native typing receipt for the emitted compatible match supplies native
typing of every real child body. Static receipts retain the original source
metadata and compiler scopes. No child evaluation premise is introduced. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildren
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates TypedLexicalWhile.Native
open CompatibleEncoding (bind_ok)

def TypedBody (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (certificate : BodyCertificate) : BodyCertificate :=
  fun scope statements code => certificate scope statements code ∧
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions

private theorem Fallback.add_typing {certificate : BodyCertificate} {scope : Scope} {result : Ty}
    {fallback : Option (List StatementId)} {code : Expr}
    (certified : Fallback certificate scope result fallback code)
    {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    Fallback (TypedBody definitions administrative type certificate) scope result fallback code := by
  cases certified with
  | none => exact .none
  | some body => exact .some ⟨body, typed⟩

private theorem matcher_typed {context : Core.Context} {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) : HasType context expression type definitions := by
  have extended := typed.rename (target := context) (mapping := Renaming.id)
    (by intro index type found; cases found)
  simpa using extended

theorem Arms.add_typing
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {source : TypedSource} {site : StatementId} {scope : Scope} {expected : TypeSystem.Ty}
    {certificate : BodyCertificate} {cases : List TypedMatchCase} {arms : List (Pattern × Expr)}
    (certified : Arms compilation source site scope expected certificate cases arms)
    {result : Ty} {fallback : Option (List StatementId)} {fallbackCode branches : Expr}
    (fallbackCertified : Fallback certificate scope result fallback fallbackCode)
    (generated : Branches compilation source scope (LocalLoop.controlType result) fallbackCode arms branches)
    {scrutinee type : Ty} {administrative : Core.Context}
    (typed : HasType (scrutinee :: (SourceCoreLocalCell.coreContext scope ++ administrative)) branches type definitions) :
    Arms compilation source site scope expected (TypedBody definitions administrative type certificate) cases arms ∧
      Fallback (TypedBody definitions administrative type certificate) scope result fallback fallbackCode := by
  induction certified generalizing branches with
  | nil =>
    cases generated
    exact ⟨.nil, Fallback.add_typing fallbackCertified (remove_front typed)⟩
  | @cons arm rest pattern body arms patternCertificate patternTyped bodyCertified tail ih =>
    cases generated with
    | cons allocation next =>
      cases typed with
      | caseE applied failed chosen =>
        cases applied with
        | apply function argument =>
          rw [sameDefinitions] at patternTyped
          have same := typing_deterministic function (matcher_typed patternTyped)
          have resultEq := (Ty.function.inj same).2
          simp only [Pattern.resultType, Ty.sum.injEq] at resultEq
          rcases resultEq with ⟨rfl, rfl⟩
          obtain ⟨nextCertified, finalFallback⟩ := ih next (remove_front failed)
          exact ⟨.cons patternCertificate (sameDefinitions.symm ▸ patternTyped)
            ⟨bodyCertified, CompatibleMatchNativeArms.bindArm_body_typing onError allocator allocation chosen⟩ nextCertified,
            finalFallback⟩

/-- The actual hidden marked allocation removes only its initializer slot.
Its subsequent load supplies the real scrutinee type to the branch fold. -/
private theorem hidden_branches
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {source : TypedSource} {scope : Scope} {binder : TypedBinder} {payload output : Ty}
    {initializer branches code : Expr} {reason : Word}
    (accepted : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Renaming.id binder output payload initializer
      (.caseE (.loadCell (.var 0)) (LanguageResult.failure output (.word reason)) branches) = .ok code)
    {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    HasType (payload :: OptionalCell.referenceType payload :: (SourceCoreLocalCell.coreContext scope ++ administrative))
      branches type definitions := by
  rw [allocator] at accepted
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocation, allocated, exactCode⟩ := bind_ok accepted
  obtain ⟨receipt, annotation, same, sameCode⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError allocated
  cases exactCode
  cases sameCode
  cases typed with
  | caseE initial failure next =>
    have bodyTyped := remove_second (absent_child receipt annotation same next)
    cases bodyTyped with
    | caseE loaded failure branch =>
      cases loaded with
      | loadCell reference =>
        cases reference with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Ty.cell.injEq, OptionalCell.referenceType,
            OptionalCell.cellType, Ty.sum.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          exact branch

theorem Certificate.typed_bodies
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason expressionCertificate bodyCertificate code)
    {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    CompatibleMatchCertificates.Certificate compilation source scope id resolution result reason expressionCertificate
      (TypedBody definitions administrative type bodyCertificate) code := by
  cases certificate with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      arms fallback branches hiddenCompiled =>
    have branchesTyped := hidden_branches onError allocator hiddenCompiled typed
    obtain ⟨nextArms, nextFallback⟩ := Arms.add_typing onError allocator sameDefinitions arms fallback branches branchesTyped
    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression sameType
      nextArms nextFallback branches hiddenCompiled

end Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeChildren
