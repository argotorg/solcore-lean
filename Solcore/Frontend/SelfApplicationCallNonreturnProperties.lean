import Solcore.Frontend.SelfApplicationNonreturnProperties

/- Actual successful references select the same finite saved closure. The body
re-enters its saved scope; unrelated caller rows never become its captured rows. -/
set_option autoImplicit false
namespace Solcore.Frontend

section
variable {source : Syntax.Expr} {name : Syntax.Identifier} {body : Syntax.Block}
variable (shape : SourceUnaryLambdaShape source name body)
variable (self : SourceSelfApplicationBody body name)
variable (savedOwner : Resolved.DeclarationId) (savedNames : LocalNameTable)
variable (savedCaptured : Resolved.LocalScope RuntimeValue)
variable (callerOwner : Resolved.DeclarationId) (callerNames : LocalNameTable)
variable (callerCaptured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
variable (callSpan argumentsSpan calleeSpan argumentSpan : Syntax.SourceSpan)
variable (calleeName argumentName : Syntax.Identifier) (calleeId argumentId : Resolved.LocalId)
variable (calleeNamed : LocalNameTable.Lookup callerNames calleeName.value calleeId)
variable (calleeFound : Resolved.LocalScope.Lookup callerCaptured calleeId
  (.sourceClosure source savedOwner savedNames savedCaptured))
variable (argumentNamed : LocalNameTable.Lookup callerNames argumentName.value argumentId)
variable (argumentFound : Resolved.LocalScope.Lookup callerCaptured argumentId
  (.sourceClosure source savedOwner savedNames savedCaptured))
include shape self calleeNamed calleeFound argumentNamed argumentFound

/-- Both input references may succeed while the self-application has no finite result. -/
theorem savedSelfApplication_none (budget : Nat) :
    evaluateClosedSourceExpression? budget callerOwner callerNames callerCaptured store
      ⟨callSpan,.call ⟨calleeSpan,.identifier calleeName⟩
        ⟨argumentsSpan,[⟨argumentSpan,.identifier argumentName⟩]⟩⟩ = none := by
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
    cases n with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ n =>
      simp only [evaluateClosedSourceExpression?,LocalNameTable.lookup?_iff.mpr calleeNamed,
        LocalNameTable.lookup?_iff.mpr argumentNamed,Resolved.LocalScope.lookup?_iff.mpr calleeFound,
        Resolved.LocalScope.lookup?_iff.mpr argumentFound,bind,Option.bind_some,pure,
        sourceUnaryLambdaShape?_iff.mpr shape,
        selfApplicationBody_none shape self savedOwner savedNames savedCaptured store (n+1)]

/-- No finite original derivation can evaluate this exact saved self-application. -/
theorem savedSelfApplication_no_original (value : RuntimeValue) (finalStore : List RuntimeValue) :
    ¬ ClosedSourceExpressionEvaluates callerOwner callerNames callerCaptured store
      ⟨callSpan,.call ⟨calleeSpan,.identifier calleeName⟩
        ⟨argumentsSpan,[⟨argumentSpan,.identifier argumentName⟩]⟩⟩ value finalStore := by
  intro original
  obtain ⟨budget,ran⟩ := evaluateClosedSourceExpression?_eventually_complete original
  have success := ran budget (Nat.le_refl budget)
  rw [savedSelfApplication_none shape self savedOwner savedNames savedCaptured callerOwner callerNames
    callerCaptured store callSpan argumentsSpan calleeSpan argumentSpan calleeName argumentName
    calleeId argumentId calleeNamed calleeFound argumentNamed argumentFound budget] at success
  cases success

end

/-- Independently created closures with self-calling bodies do not return, even at distinct source occurrences. -/
theorem directSelfApplication_none
    {left right : Syntax.Expr} {leftName rightName : Syntax.Identifier} {leftBody rightBody : Syntax.Block}
    (leftShape : SourceUnaryLambdaShape left leftName leftBody) (leftSelf : SourceSelfApplicationBody leftBody leftName)
    (rightShape : SourceUnaryLambdaShape right rightName rightBody) (rightSelf : SourceSelfApplicationBody rightBody rightName)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (callSpan argumentsSpan : Syntax.SourceSpan) (budget : Nat) :
    evaluateClosedSourceExpression? budget owner names captured store
      ⟨callSpan,.call left ⟨argumentsSpan,[right]⟩⟩ = none := by
  have creation {source name body} (shape : SourceUnaryLambdaShape source name body) (n : Nat) :
      evaluateClosedSourceExpression? (n+1) owner names captured store source =
        some (.sourceClosure source owner names captured,store) := by
    cases shape <;> simp only [evaluateClosedSourceExpression?,sourceUnaryLambdaShape?,bind,Option.bind_some,pure]
  cases budget with
  | zero => simp [evaluateClosedSourceExpression?]
  | succ n =>
    cases n with
    | zero => simp [evaluateClosedSourceExpression?]
    | succ n =>
      simp only [evaluateClosedSourceExpression?,creation leftShape n,creation rightShape n,bind,Option.bind_some,
        sourceUnaryLambdaShape?_iff.mpr leftShape,
        selfApplicationBody_boundSelf_none rightShape rightSelf leftSelf owner owner names names captured captured store (n+1)]

/-- The direct raw self-call has no finite original successful endpoint. -/
theorem directSelfApplication_no_original
    {left right : Syntax.Expr} {leftName rightName : Syntax.Identifier} {leftBody rightBody : Syntax.Block}
    (leftShape : SourceUnaryLambdaShape left leftName leftBody) (leftSelf : SourceSelfApplicationBody leftBody leftName)
    (rightShape : SourceUnaryLambdaShape right rightName rightBody) (rightSelf : SourceSelfApplicationBody rightBody rightName)
    (owner : Resolved.DeclarationId) (names : LocalNameTable) (captured : Resolved.LocalScope RuntimeValue)
    (store : List RuntimeValue) (callSpan argumentsSpan : Syntax.SourceSpan)
    (value : RuntimeValue) (finalStore : List RuntimeValue) :
    ¬ ClosedSourceExpressionEvaluates owner names captured store
      ⟨callSpan,.call left ⟨argumentsSpan,[right]⟩⟩ value finalStore := by
  intro original
  obtain ⟨budget,ran⟩ := evaluateClosedSourceExpression?_eventually_complete original
  have success := ran budget (Nat.le_refl budget)
  rw [directSelfApplication_none leftShape leftSelf rightShape rightSelf owner names captured store callSpan argumentsSpan budget] at success
  cases success

end Solcore.Frontend
