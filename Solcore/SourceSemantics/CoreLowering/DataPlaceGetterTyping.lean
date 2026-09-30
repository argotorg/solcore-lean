import Solcore.Frontend.SourceCoreDataPlaces

/-! Getter typing comes from the real enclosing Core checker. Finite-well-
formed catalog definitions alone do not authenticate nominal row completeness.
No runtime evaluation premise is used in this extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceGetterTyping
open Core Frontend SourceCoreDataPlaces

theorem of_execute {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (typed : HasType context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      resultType definitions) :
    HasType (keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions := by
  unfold execute LanguageResult.bind at typed
  cases typed with
  | letE reference body =>
    cases body with
    | caseE keys failure success =>
      cases success with
      | caseE snapshot failure success =>
        cases snapshot with
        | apply function argument =>
          cases function with
          | lambda parameterTyped resultTyped body =>
            cases argument with
            | pair referenceArgument keyArgument =>
              cases referenceArgument with
              | loadCell referenceTyped =>
                cases referenceTyped with
                | var referenceAt =>
                  cases keyArgument with
                  | var keyAt =>
                    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at referenceAt keyAt
                    subst_vars
                    exact .apply (.lambda parameterTyped resultTyped body) (.pair (.loadCell (.var rfl)) (.var rfl))

/-- Direct consumer of an actual successful whole-expression inference. -/
theorem of_infer {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (accepted : infer? context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      definitions = some resultType) :
    HasType (keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions :=
  of_execute (infer_sound accepted)

end Solcore.SourceSemantics.CoreLowering.DataPlaceGetterTyping
