import Solcore.Frontend.SourceCoreCompatibleDataPlaces

/-! Getter typing comes from the real enclosing Core checker. Finite-well-
formed catalog definitions alone do not authenticate nominal row completeness.
No runtime evaluation premise is used in this extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceHelperTyping
open Core Frontend SourceCoreCompatibleDataPlaces

theorem getter_of_execute {definitions : DataEnvironment} {context : Core.Context}
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
theorem getter_of_infer {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (accepted : infer? context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      definitions = some resultType) :
    HasType (keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions :=
  getter_of_execute (infer_sound accepted)

/-- The retained child typing fixes the otherwise unused RHS slot. This is a
static compiler obligation and does not assume any child evaluation. -/
theorem setter_of_execute_rhs {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType rhsType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (typed : HasType context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      resultType definitions)
    (rhsTyped : HasType (prepared.optionalLeaf :: keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (shift 3 rhs) (LanguageResult.resultType rhsType) definitions) :
    HasType (prepared.route.leafType :: rhsType :: prepared.optionalLeaf :: keys.type ::
        OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) definitions := by
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
                    cases success with
                    | caseE right failure success =>
                      have same := typing_deterministic right rhsTyped
                      cases same
                      cases success with
                      | caseE modified failure success =>
                        cases success with
                        | caseE written failure success =>
                          cases written with
                          | apply function argument =>
                            cases function with
                            | lambda parameterTyped resultTyped body =>
                              cases argument with
                              | pair referenceArgument rest =>
                                cases rest with
                                | pair keys replacement =>
                                  cases replacement with
                                  | var replacementAt =>
                                    simp only [List.getElem?_cons_zero, Option.some.injEq] at replacementAt
                                    subst_vars
                                    exact .apply (.lambda parameterTyped resultTyped body) (.pair referenceArgument (.pair keys (.var rfl)))

theorem setter_of_execute {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {reference rhs next : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {outputType resultType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word}
    (typed : HasType context (execute prepared reference keys rhs next outputType operator bitNot invalid)
      resultType definitions)
    (rhsTyped : HasType (prepared.optionalLeaf :: keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (shift 3 rhs) (LanguageResult.resultType prepared.route.leafType) definitions) :
    HasType (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: keys.type ::
        OptionalCell.referenceType prepared.route.rootType :: context)
      (.apply (setter prepared keys.type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) definitions :=
  setter_of_execute_rhs typed rhsTyped

/-- Ordinary child typing yields the exact three administrative slots used by
execute. This is syntactic weakening only; store values are never compared. -/
theorem rhs_shift_typed_rhs {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {rhsType : Ty} {keys : SourceCoreBasic.LoweredExpr} {rhs : Expr}
    (typed : HasType context rhs (LanguageResult.resultType rhsType) definitions) :
    HasType (prepared.optionalLeaf :: keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (shift 3 rhs) (LanguageResult.resultType rhsType) definitions := by
  simpa only [shift, List.range, List.range.loop, List.foldl, Core.Context.insertAt] using
    (((typed.weakenAt (inserted := OptionalCell.referenceType prepared.route.rootType) 0).weakenAt (inserted := keys.type) 0).weakenAt
      (inserted := prepared.optionalLeaf) 0)
theorem rhs_shift_typed {definitions : DataEnvironment} {context : Core.Context}
    {prepared : Prepared} {keys : SourceCoreBasic.LoweredExpr} {rhs : Expr}
    (typed : HasType context rhs (LanguageResult.resultType prepared.route.leafType) definitions) :
    HasType (prepared.optionalLeaf :: keys.type :: OptionalCell.referenceType prepared.route.rootType :: context)
      (shift 3 rhs) (LanguageResult.resultType prepared.route.leafType) definitions :=
  rhs_shift_typed_rhs typed

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceHelperTyping
