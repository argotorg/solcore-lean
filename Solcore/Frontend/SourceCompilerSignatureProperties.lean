import Solcore.Frontend.SourceRuntimeLinking

/-! Type-projection coherence shared by the direct-Core and finite-graph
backends.  The finite graph additionally supports source function types, so
the implication runs from the smaller direct-Core domain to the graph domain. -/

set_option autoImplicit false

namespace Solcore.Frontend

open TypeSystem

/-- Every result type admitted by direct Core has the same backend-native
projection in the finite call graph. -/
theorem sourceCore_lowerType_implies_graph_lowerType
    (site : SourceCoreElaboration.ErrorSite) (sourceType : Ty)
    (coreType : Core.Ty)
    (accepted : SourceCoreElaboration.lowerType site sourceType = .ok coreType) :
    SourceRuntimeLinking.lowerType sourceType = .ok coreType := by
  induction sourceType generalizing coreType with
  | «variable» id =>
      exact nomatch accepted
  | parameter id =>
      exact nomatch accepted
  | constructor id =>
      cases id with
      | builtin builtin =>
          cases builtin with
          | unit => cases accepted; rfl
          | bool => cases accepted; rfl
          | word => cases accepted; rfl
          | integer => exact nomatch accepted
      | declaration id =>
          exact nomatch accepted
  | application function argument ihFunction ihArgument =>
      unfold SourceCoreElaboration.lowerType at accepted
      split at accepted <;> exact nomatch accepted
  | function parameter result ihParameter ihResult =>
      exact nomatch accepted
  | product left right ihLeft ihRight =>
      simp only [SourceCoreElaboration.lowerType] at accepted
      cases leftProjection : SourceCoreElaboration.lowerType site left with
      | error error =>
          simp [leftProjection, bind, Except.bind] at accepted
      | ok loweredLeft =>
          cases rightProjection : SourceCoreElaboration.lowerType site right with
          | error error =>
              simp [leftProjection, rightProjection, bind, Except.bind] at accepted
          | ok loweredRight =>
              simp [leftProjection, rightProjection, bind, Except.bind] at accepted
              cases accepted
              simp [SourceRuntimeLinking.lowerType,
                ihLeft loweredLeft leftProjection,
                ihRight loweredRight rightProjection, bind, Except.bind,
                pure, Pure.pure, Except.pure]
  | mapping key value ihKey ihValue =>
      exact nomatch accepted
  | proxy inner ih =>
      exact nomatch accepted
  | comptime inner ih =>
      exact nomatch accepted
  | error =>
      exact nomatch accepted

/-- The graph-only closure/function case extends the direct-Core projection. -/
theorem graph_lowerType_function {parameter result : Ty}
    {loweredParameter loweredResult : Core.Ty}
    (parameterAccepted : SourceRuntimeLinking.lowerType parameter =
      .ok loweredParameter)
    (resultAccepted : SourceRuntimeLinking.lowerType result =
      .ok loweredResult) :
    SourceRuntimeLinking.lowerType (.function parameter result) =
      .ok (.function loweredParameter loweredResult) := by
  simp [SourceRuntimeLinking.lowerType, parameterAccepted, resultAccepted,
    bind, Except.bind, pure, Pure.pure, Except.pure]

/-- Both backends agree on products, including products whose components are
themselves function types only in the graph backend. -/
theorem graph_lowerType_product {left right : Ty}
    {loweredLeft loweredRight : Core.Ty}
    (leftAccepted : SourceRuntimeLinking.lowerType left = .ok loweredLeft)
    (rightAccepted : SourceRuntimeLinking.lowerType right = .ok loweredRight) :
    SourceRuntimeLinking.lowerType (.product left right) =
      .ok (.product loweredLeft loweredRight) := by
  simp [SourceRuntimeLinking.lowerType, leftAccepted, rightAccepted,
    bind, Except.bind, pure, Pure.pure, Except.pure]

end Solcore.Frontend
