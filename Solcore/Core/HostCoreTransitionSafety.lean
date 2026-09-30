import Solcore.Core.HostStateSafety

/-! Preservation of host-aware state typing by ordinary Core transitions. -/

set_option autoImplicit false

namespace Solcore.Core

theorem transition_preserves_host_state_type
    {definitions : DataEnvironment}
    {state next : State} {resultType : Ty}
    (stateTyping : HostStateHasType state resultType definitions)
    (transition : Transition state next) :
    HostStateHasType next resultType definitions := by
  cases transition with
  | unit =>
      cases stateTyping with
      | eval store env expr cont => cases expr; exact .ret store .unit cont
  | bool =>
      cases stateTyping with
      | eval store env expr cont => cases expr; exact .ret store .bool cont
  | word =>
      cases stateTyping with
      | eval store env expr cont => cases expr; exact .ret store .word cont
  | integer =>
      cases stateTyping with
      | eval store env expr cont => cases expr; exact .ret store .integer cont
  | enterPair =>
      cases stateTyping with
      | eval store env expr cont =>
          cases expr with
          | pair left right => exact .eval store env left (.cons (.pairRight env right) cont)
  | enterPairRight =>
      cases stateTyping with
      | ret store left cont =>
          cases cont with
          | cons frame rest => cases frame with
            | pairRight env right => exact .eval store env right (.cons (.pairApply left) rest)
  | applyPair =>
      cases stateTyping with
      | ret store right cont => cases cont with
        | cons frame rest => cases frame with
          | pairApply left => exact .ret store (.pair left right) rest
  | enterFirst =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | first operand => exact .eval store env operand (.cons .firstApply cont)
  | applyFirst =>
      cases stateTyping with
      | ret store pair cont => cases cont with
        | cons frame rest => cases frame with
          | firstApply => cases pair with
            | pair left _ => exact .ret store left rest
  | enterSecond =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | second operand => exact .eval store env operand (.cons .secondApply cont)
  | applySecond =>
      cases stateTyping with
      | ret store pair cont => cases cont with
        | cons frame rest => cases frame with
          | secondApply => cases pair with
            | pair _ right => exact .ret store right rest
  | enterInLeft =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | inLeft _ payload => exact .eval store env payload (.cons .inLeftApply cont)
  | applyInLeft =>
      cases stateTyping with
      | ret store payload cont => cases cont with
        | cons frame rest => cases frame with
          | inLeftApply => exact .ret store (.inLeft payload) rest
  | enterInRight =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | inRight _ payload => exact .eval store env payload (.cons .inRightApply cont)
  | applyInRight =>
      cases stateTyping with
      | ret store payload cont => cases cont with
        | cons frame rest => cases frame with
          | inRightApply => exact .ret store (.inRight payload) rest
  | enterCase =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | caseE scrutinee left right =>
            exact .eval store env scrutinee (.cons (.caseBranches env left right) cont)
  | chooseLeft =>
      cases stateTyping with
      | ret store sum cont => cases cont with
        | cons frame rest => cases frame with
          | caseBranches env left right => cases sum with
            | inLeft payload => exact .eval store (.cons payload env) left rest
  | chooseRight =>
      cases stateTyping with
      | ret store sum cont => cases cont with
        | cons frame rest => cases frame with
          | caseBranches env left right => cases sum with
            | inRight payload => exact .eval store (.cons payload env) right rest
  | enterNewCell =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | newCell initializer =>
            exact .eval store env initializer (.cons .newCellApply cont)
  | @applyNewCell elementType initialValue continuation store =>
      cases stateTyping with
      | @ret _ world _ _ _ _ _ storeTyping valueTyping cont => cases cont with
        | cons frame rest => cases frame with
          | newCellApply =>
              let futureWorld := world ++ [elementType]
              have extension : WorldExtends world futureWorld := ⟨[elementType], rfl⟩
              have futureStore : HostStoreHasTypes futureWorld (store.allocate initialValue).1 definitions := by
                simpa [futureWorld] using storeTyping.allocate valueTyping
              have fresh : futureWorld[(store.allocate initialValue).2]? = some elementType := by
                simp [futureWorld, Store.allocate, ← storeTyping.length_eq]
              exact .ret futureStore (.cellRef fresh) (rest.weaken extension)
  | enterLoadCell =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | loadCell reference =>
            exact .eval store env reference (.cons .loadCellApply cont)
  | applyLoadCell loaded =>
      cases stateTyping with
      | ret store cell cont => cases cont with
        | cons frame rest => cases frame with
          | loadCellApply => cases cell with
            | cellRef found =>
                obtain ⟨stored, read, typing⟩ := store.lookup found
                rw [loaded] at read
                cases read
                exact .ret store typing rest
  | enterStoreCell =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | storeCell reference value =>
            exact .eval store env reference (.cons (.storeCellValue env value) cont)
  | beginStoreCellValue _ =>
      cases stateTyping with
      | ret store cell cont => cases cont with
        | cons frame rest => cases frame with
          | storeCellValue env value => cases cell with
            | cellRef found => exact .eval store env value (.cons (.storeCellApply found) rest)
  | applyStoreCell written =>
      cases stateTyping with
      | ret store value cont => cases cont with
        | cons frame rest => cases frame with
          | storeCellApply found =>
              exact .ret (store.write found value written) .unit rest
  | enterConstruct =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | construct lookup payload => exact .eval store env payload (.cons (.constructApply lookup) cont)
  | applyConstruct =>
      cases stateTyping with
      | ret store payload cont => cases cont with
        | cons frame rest => cases frame with
          | constructApply lookup => exact .ret store (.constructed lookup payload) rest
  | enterMatchData =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | matchData lookup _ scrutinee branches =>
            exact .eval store env scrutinee (.cons (.matchDataApply lookup env branches) cont)
  | chooseData ownerEq branchLookup =>
      cases stateTyping with
      | ret store data cont => cases cont with
        | cons frame rest => cases frame with
          | matchDataApply definitionLookup env branches => cases data with
            | constructed constructorLookup payload =>
                obtain ⟨_, runtimeLookup, payloadLookup⟩ :=
                  DataEnvironment.lookupConstructorPayloadType?_eq_some_iff.mp constructorLookup
                rw [ownerEq] at runtimeLookup
                have typedLookup := DataEnvironment.lookupDataType?_eq_some_iff.mp definitionLookup
                rw [typedLookup] at runtimeLookup
                cases runtimeLookup
                exact .eval store (.cons payload env)
                  (branches.lookup payloadLookup branchLookup) rest
  | lambda =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | lambda _ _ body => exact .ret store (.closure env body) cont
  | enterApply =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | apply function argument =>
            exact .eval store env function (.cons (.applyArgument env argument) cont)
  | beginArgument =>
      cases stateTyping with
      | ret store function cont => cases cont with
        | cons frame rest => cases frame with
          | applyArgument caller argument => cases function with
            | closure captured body =>
                exact .eval store caller argument (.cons (.applyClosure captured body) rest)
  | invokeClosure =>
      cases stateTyping with
      | ret store argument cont => cases cont with
        | cons frame rest => cases frame with
          | applyClosure captured body =>
              exact .eval store (.cons argument captured) body rest
  | var valueLookup =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | var typeLookup =>
            obtain ⟨found, foundLookup, foundTyping⟩ := env.lookup typeLookup
            rw [valueLookup] at foundLookup
            cases foundLookup
            exact .ret store foundTyping cont
  | enterUnary =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | unary operand => exact .eval store env operand (.cons .unaryApply cont)
  | applyUnary applied =>
      cases stateTyping with
      | ret store operand cont => cases cont with
        | cons frame rest => cases frame with
          | unaryApply =>
              exact .ret store (RuntimeValueHasType.toHost
                (unary_apply_result_has_runtime_type applied definitions)) rest
  | enterBinary =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | binary left right => exact .eval store env left (.cons (.binaryRight env right) cont)
  | enterBinaryRight =>
      cases stateTyping with
      | ret store left cont => cases cont with
        | cons frame rest => cases frame with
          | binaryRight env right => exact .eval store env right (.cons (.binaryApply left) rest)
  | applyBinary applied =>
      cases stateTyping with
      | ret store right cont => cases cont with
        | cons frame rest => cases frame with
          | binaryApply left =>
              exact .ret store (RuntimeValueHasType.toHost
                (binary_apply_result_has_runtime_type applied definitions)) rest
  | enterTernary =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | ternary first second third =>
            exact .eval store env first (.cons (.ternarySecond env second third) cont)
  | enterTernarySecond =>
      cases stateTyping with
      | ret store first cont => cases cont with
        | cons frame rest => cases frame with
          | ternarySecond env second third =>
              exact .eval store env second (.cons (.ternaryThird first env third) rest)
  | enterTernaryThird =>
      cases stateTyping with
      | ret store second cont => cases cont with
        | cons frame rest => cases frame with
          | ternaryThird first env third =>
              exact .eval store env third (.cons (.ternaryApply first second) rest)
  | applyTernary applied =>
      cases stateTyping with
      | ret store third cont => cases cont with
        | cons frame rest => cases frame with
          | ternaryApply first second =>
              exact .ret store (RuntimeValueHasType.toHost
                (ternary_apply_result_has_runtime_type applied definitions)) rest
  | enterLet =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | letE bound body => exact .eval store env bound (.cons (.letBody env body) cont)
  | bindLet =>
      cases stateTyping with
      | ret store value cont => cases cont with
        | cons frame rest => cases frame with
          | letBody env body => exact .eval store (.cons value env) body rest
  | enterIf =>
      cases stateTyping with
      | eval store env expr cont => cases expr with
        | ifE condition thenType elseType =>
            exact .eval store env condition (.cons (.ifBranches env thenType elseType) cont)
  | chooseTrue =>
      cases stateTyping with
      | ret store value cont => cases cont with
        | cons frame rest => cases frame with
          | ifBranches env thenType elseType => exact .eval store env thenType rest
  | chooseFalse =>
      cases stateTyping with
      | ret store value cont => cases cont with
        | cons frame rest => cases frame with
          | ifBranches env thenType elseType => exact .eval store env elseType rest

end Solcore.Core
