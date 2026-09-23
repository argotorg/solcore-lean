import Solcore.SourceSemantics.Requirements

/-!
Declarative source-operator typing.

Primitive operators are listed directly.  User-defined operator behavior is
validated against the resolved trait catalog and the exact retained evidence;
no overload selector or trait-search procedure is invoked here.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend
open Frontend.SourceInference

/-- Arithmetic and bitwise binary spellings whose primitive result has the
same type as both operands. -/
inductive ArithmeticBinaryOperator : Syntax.BinaryOp → Prop where
  | multiply : ArithmeticBinaryOperator .multiply
  | divide : ArithmeticBinaryOperator .divide
  | modulo : ArithmeticBinaryOperator .modulo
  | add : ArithmeticBinaryOperator .add
  | subtract : ArithmeticBinaryOperator .subtract
  | bitAnd : ArithmeticBinaryOperator .bitAnd
  | bitXor : ArithmeticBinaryOperator .bitXor
  | bitOr : ArithmeticBinaryOperator .bitOr

/-- Comparison spellings whose primitive result is Boolean. -/
inductive ComparisonBinaryOperator : Syntax.BinaryOp → Prop where
  | less : ComparisonBinaryOperator .less
  | greater : ComparisonBinaryOperator .greater
  | lessEqual : ComparisonBinaryOperator .lessEqual
  | greaterEqual : ComparisonBinaryOperator .greaterEqual
  | equal : ComparisonBinaryOperator .equal
  | notEqual : ComparisonBinaryOperator .notEqual

/-- The source spelling-to-trait-method assignment for operator forms which
remain operator nodes after resolution. -/
inductive BinaryTraitDispatch : Syntax.BinaryOp → String → String → Prop where
  | multiply : BinaryTraitDispatch .multiply "Mul" "mul"
  | divide : BinaryTraitDispatch .divide "Div" "div"
  | modulo : BinaryTraitDispatch .modulo "Mod" "mod"
  | add : BinaryTraitDispatch .add "Add" "add"
  | subtract : BinaryTraitDispatch .subtract "Sub" "sub"
  | bitAnd : BinaryTraitDispatch .bitAnd "BitAnd" "band"
  | bitXor : BinaryTraitDispatch .bitXor "BitXor" "bxor"
  | bitOr : BinaryTraitDispatch .bitOr "BitOr" "bor"
  | greater : BinaryTraitDispatch .greater "Ord" "gt"
  | equal : BinaryTraitDispatch .equal "Eq" "eq"

/-- Unary operator forms with trait dispatch. -/
inductive UnaryTraitDispatch : Syntax.UnaryOp → String → String → Prop where
  | bitNot : UnaryTraitDispatch .bitNot "BitNot" "bnot"

/-- A uniquely named operator method has the required instantiated signature
and produces the declaration-ordered primary and method predicates. -/
inductive OperatorProfileInstantiates
    (context : Context) (traitName methodName : String)
    (operand : TypeSystem.Ty) (parameterTypes returnTypes : List TypeSystem.Ty) :
    List ProgramPredicate → Prop where
  | intro
      {signature : ProgramTraitSignature}
      {method : ProgramTraitMethodSignature}
      {parameter : TypeSystem.TypeParameterId}
      (signature_mem : signature ∈ context.signatures.traits)
      (trait_name_eq : signature.name = traitName)
      (parameters_eq : signature.parameters = [parameter])
      (method_unique :
        signature.methods.filter (fun candidate => candidate.name == methodName) =
          [method])
      (parameter_types_eq :
        method.parameterTypes.map
          (TypeSystem.ParameterSubstitution.apply [(parameter, operand)]) =
            parameterTypes)
      (return_types_eq :
        method.returnTypes.map
          (TypeSystem.ParameterSubstitution.apply [(parameter, operand)]) =
            returnTypes) :
      OperatorProfileInstantiates context traitName methodName operand
        parameterTypes returnTypes
        ({ trait := .declaration signature.id, subject := operand, arguments := [] } ::
          method.wherePredicates.map
            (ProgramPredicate.applyParameters [(parameter, operand)]))

/-- Complete unary source-operator typing, including exact evidence IDs. -/
inductive UnaryOperatorHasType (context : Context) :
    Syntax.UnaryOp → TypeSystem.Ty → TypeSystem.Ty →
      List RequirementId → Prop where
  | logicalNot : UnaryOperatorHasType context .logicalNot .bool .bool []
  | wordBitNot : UnaryOperatorHasType context .bitNot .word .word []
  | integerBitNot : UnaryOperatorHasType context .bitNot .integer .integer []
  | trait
      {operator : Syntax.UnaryOp}
      {traitName methodName : String}
      {operand result : TypeSystem.Ty}
      {predicates : List ProgramPredicate}
      {requirements : List RequirementId}
      (dispatch : UnaryTraitDispatch operator traitName methodName)
      (profile : OperatorProfileInstantiates context traitName methodName
        operand [operand] [result] predicates)
      (evidence : RequirementSequenceProves context requirements predicates) :
      UnaryOperatorHasType context operator operand result requirements

/-- Complete binary source-operator typing, including exact evidence IDs. -/
inductive BinaryOperatorHasType (context : Context) :
    Syntax.BinaryOp → TypeSystem.Ty → TypeSystem.Ty → TypeSystem.Ty →
      List RequirementId → Prop where
  | wordArithmetic {operator : Syntax.BinaryOp}
      (kind : ArithmeticBinaryOperator operator) :
      BinaryOperatorHasType context operator .word .word .word []
  | integerArithmetic {operator : Syntax.BinaryOp}
      (kind : ArithmeticBinaryOperator operator) :
      BinaryOperatorHasType context operator .integer .integer .integer []
  | wordComparison {operator : Syntax.BinaryOp}
      (kind : ComparisonBinaryOperator operator) :
      BinaryOperatorHasType context operator .word .word .bool []
  | integerComparison {operator : Syntax.BinaryOp}
      (kind : ComparisonBinaryOperator operator) :
      BinaryOperatorHasType context operator .integer .integer .bool []
  | booleanAnd :
      BinaryOperatorHasType context .logicalAnd .bool .bool .bool []
  | booleanOr :
      BinaryOperatorHasType context .logicalOr .bool .bool .bool []
  | trait
      {operator : Syntax.BinaryOp}
      {traitName methodName : String}
      {operand result : TypeSystem.Ty}
      {predicates : List ProgramPredicate}
      {requirements : List RequirementId}
      (dispatch : BinaryTraitDispatch operator traitName methodName)
      (profile : OperatorProfileInstantiates context traitName methodName
        operand [operand, operand] [result] predicates)
      (evidence : RequirementSequenceProves context requirements predicates) :
      BinaryOperatorHasType context operator operand operand result requirements

namespace UnaryOperatorHasType

theorem requirements_valid
    {context : Context} {operator : Syntax.UnaryOp}
    {operand result : TypeSystem.Ty} {requirements : List RequirementId}
    (typing : UnaryOperatorHasType context operator operand result requirements) :
    RequirementIdsValid context requirements := by
  cases typing with
  | logicalNot | wordBitNot | integerBitNot => simp [RequirementIdsValid]
  | trait _ _ evidence => exact evidence.ids_valid

end UnaryOperatorHasType

namespace BinaryOperatorHasType

theorem requirements_valid
    {context : Context} {operator : Syntax.BinaryOp}
    {left right result : TypeSystem.Ty} {requirements : List RequirementId}
    (typing : BinaryOperatorHasType context operator left right result requirements) :
    RequirementIdsValid context requirements := by
  cases typing with
  | wordArithmetic | integerArithmetic | wordComparison | integerComparison |
      booleanAnd | booleanOr => simp [RequirementIdsValid]
  | trait _ _ evidence => exact evidence.ids_valid

end BinaryOperatorHasType

end Solcore.SourceSemantics
