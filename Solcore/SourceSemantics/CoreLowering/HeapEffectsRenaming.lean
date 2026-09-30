import Solcore.SourceSemantics.CoreLowering.ReadOnlyRenaming

/-! Exact binder insertion for Core expressions that may allocate, load, and
write existing values, but do not create or call closures. Mutation preserves
the original value and store under renaming because no capture environment is
rebuilt. Administrative closure cells are allowed in the initial store. -/

set_option autoImplicit false

namespace Solcore.Core.HeapEffects

inductive Expression : Expr → Prop where
  | unit : Expression .unit
  | bool {value} : Expression (.bool value)
  | word {value} : Expression (.word value)
  | var {index} : Expression (.var index)
  | pair {left right} : Expression left → Expression right → Expression (.pair left right)
  | first {operand} : Expression operand → Expression (.first operand)
  | second {operand} : Expression operand → Expression (.second operand)
  | inLeft {type payload} : Expression payload → Expression (.inLeft type payload)
  | inRight {type payload} : Expression payload → Expression (.inRight type payload)
  | caseE {scrutinee left right} : Expression scrutinee → Expression left → Expression right →
      Expression (.caseE scrutinee left right)
  | newCell {type initializer} : Expression initializer → Expression (.newCell type initializer)
  | storeCell {reference value} : Expression reference → Expression value → Expression (.storeCell reference value)
  | loadCell {reference} : Expression reference → Expression (.loadCell reference)
  | unary {operator operand} : Expression operand → Expression (.unary operator operand)
  | binary {operator left right} : Expression left → Expression right → Expression (.binary operator left right)
  | ternary {operator first second third} : Expression first → Expression second → Expression third →
      Expression (.ternary operator first second third)
  | letE {value body} : Expression value → Expression body → Expression (.letE value body)
  | ifE {condition left right} : Expression condition → Expression left → Expression right →
      Expression (.ifE condition left right)

theorem Expression.of_readOnly {expression : Expr} (restricted : ReadOnly.Expression expression) :
    Expression expression := by
  induction restricted with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var => exact .var
  | pair _ _ left right => exact .pair left right
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih
  | inLeft _ ih => exact .inLeft ih
  | inRight _ ih => exact .inRight ih
  | caseE _ _ _ scrutinee left right => exact .caseE scrutinee left right
  | loadCell _ ih => exact .loadCell ih
  | unary _ ih => exact .unary ih
  | binary _ _ left right => exact .binary left right
  | ternary _ _ _ first second third => exact .ternary first second third
  | letE _ _ value body => exact .letE value body
  | ifE _ _ _ condition left right => exact .ifE condition left right

theorem Expression.rename {expression : Expr} (restricted : Expression expression) (mapping : Renaming) :
    Expression (expression.rename mapping) := by
  induction restricted generalizing mapping with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var => exact .var
  | pair _ _ left right => exact .pair (left mapping) (right mapping)
  | first _ ih => exact .first (ih mapping)
  | second _ ih => exact .second (ih mapping)
  | inLeft _ ih => exact .inLeft (ih mapping)
  | inRight _ ih => exact .inRight (ih mapping)
  | caseE _ _ _ scrutinee left right => exact .caseE (scrutinee mapping) (left mapping.lift) (right mapping.lift)
  | newCell _ ih => exact .newCell (ih mapping)
  | storeCell _ _ reference value => exact .storeCell (reference mapping) (value mapping)
  | loadCell _ ih => exact .loadCell (ih mapping)
  | unary _ ih => exact .unary (ih mapping)
  | binary _ _ left right => exact .binary (left mapping) (right mapping)
  | ternary _ _ _ first second third => exact .ternary (first mapping) (second mapping) (third mapping)
  | letE _ _ value body => exact .letE (value mapping) (body mapping.lift)
  | ifE _ _ _ condition left right => exact .ifE (condition mapping) (left mapping) (right mapping)

theorem Expression.weakenAt {expression : Expr} (restricted : Expression expression) (cutoff : Nat) :
    Expression (expression.weakenAt cutoff) := by
  simpa using restricted.rename (Renaming.insertion cutoff)

/-- Transport an existing finite evaluation using the syntax restriction and
lookup agreement. No store typing or first-order payload premise is needed. -/
theorem Expression.evaluation_rename {expression : Expr} (restricted : Expression expression)
    {environment target : Environment} {before after : Store} {result : Value} {mapping : Renaming}
    (evaluation : Evaluates environment before expression result after)
    (related : ReadOnly.EnvironmentsAgree mapping environment target) :
    Evaluates target before (expression.rename mapping) result after := by
  induction restricted generalizing environment target before after result mapping with
  | unit => cases evaluation; exact .unit
  | bool => cases evaluation; exact .bool
  | word => cases evaluation; exact .word
  | var => cases evaluation with | var found => exact .var (related found)
  | pair _ _ left right =>
      cases evaluation with
      | pair leftEvaluation rightEvaluation => exact .pair (left leftEvaluation related) (right rightEvaluation related)
  | first _ ih => cases evaluation with | first evaluated => exact .first (ih evaluated related)
  | second _ ih => cases evaluation with | second evaluated => exact .second (ih evaluated related)
  | inLeft _ ih => cases evaluation with | inLeft evaluated => exact .inLeft (ih evaluated related)
  | inRight _ ih => cases evaluation with | inRight evaluated => exact .inRight (ih evaluated related)
  | caseE _ _ _ scrutinee left right =>
      cases evaluation with
      | caseLeft selected branch => exact .caseLeft (scrutinee selected related) (left branch (related.lift _))
      | caseRight selected branch => exact .caseRight (scrutinee selected related) (right branch (related.lift _))
  | newCell _ ih => cases evaluation with | newCell evaluated => exact .newCell (ih evaluated related)
  | storeCell _ _ reference value =>
      cases evaluation with
      | storeCell referenceEvaluation read valueEvaluation written =>
          exact .storeCell (reference referenceEvaluation related) read (value valueEvaluation related) written
  | loadCell _ ih =>
      cases evaluation with
      | loadCell reference read => exact .loadCell (ih reference related) read
  | unary _ ih => cases evaluation with | unary evaluated applied => exact .unary (ih evaluated related) applied
  | binary _ _ left right =>
      cases evaluation with
      | binary leftEvaluation rightEvaluation applied =>
          exact .binary (left leftEvaluation related) (right rightEvaluation related) applied
  | ternary _ _ _ first second third =>
      cases evaluation with
      | ternary firstEvaluation secondEvaluation thirdEvaluation applied =>
          exact .ternary (first firstEvaluation related) (second secondEvaluation related) (third thirdEvaluation related) applied
  | letE _ _ value body =>
      cases evaluation with
      | letE evaluated branch => exact .letE (value evaluated related) (body branch (related.lift _))
  | ifE _ _ _ condition left right =>
      cases evaluation with
      | ifTrue selected branch => exact .ifTrue (condition selected related) (left branch related)
      | ifFalse selected branch => exact .ifFalse (condition selected related) (right branch related)

theorem Expression.evaluation_weakenAt {expression : Expr} (restricted : Expression expression)
    {environment : Environment} {before after : Store} {result : Value}
    (evaluation : Evaluates environment before expression result after) (cutoff : Nat) (inserted : Value) :
    Evaluates (Environment.insertAt environment cutoff inserted) before (expression.weakenAt cutoff) result after := by
  simpa using restricted.evaluation_rename evaluation (ReadOnly.EnvironmentsAgree.insertion environment cutoff inserted)

theorem Expression.evaluation_weakenAt_zero {expression : Expr} (restricted : Expression expression)
    {environment : Environment} {before after : Store} {result : Value}
    (evaluation : Evaluates environment before expression result after) (inserted : Value) :
    Evaluates (inserted :: environment) before (expression.weakenAt 0) result after := by
  simpa [Environment.insertAt] using restricted.evaluation_weakenAt evaluation 0 inserted

end Solcore.Core.HeapEffects
