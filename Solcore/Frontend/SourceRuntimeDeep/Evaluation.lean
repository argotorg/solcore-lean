import Solcore.Frontend.SourceRuntimeDeep.Application

/-! Deep preservation for the individual graph evaluator branches. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- The local-variable evaluator case uses the same keyed lookup certified by
the static context, so it cannot return an untyped captured value. -/
theorem evaluate_local_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store} {id : Resolved.LocalId}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context (.local id) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store (.local id) =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  cases staticFound : lookupStatic? context id with
  | none => simp [infer, staticFound] at inferredAt
  | some staticType =>
      simp [infer, staticFound] at inferredAt
      cases inferredAt
      obtain ⟨foundValue, valueFound, valueTyping⟩ :=
        environmentTyping.lookup staticFound
      cases fuel with
      | zero => simp [evaluate] at completed
      | succ remaining =>
          have completed' : RunResult.done foundValue store =
              .done value finalStore := by
            simpa [evaluate, valueFound] using completed
          cases completed'
          exact ⟨world, .refl world, storeTyping,
            by simpa [resultType] using valueTyping⟩

theorem evaluate_unit_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (_environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context .unit expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store .unit =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  simp [infer] at inferredAt
  cases inferredAt
  have expectedEq : expected = .unit := by
    simpa [StaticType.erase] using resultType.symm
  subst expected
  cases fuel with
  | zero => simp [evaluate] at completed
  | succ remaining =>
      have completed' : RunResult.done .unit store =
          .done value finalStore := by
        simpa [evaluate] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping,
        Value.GraphHasType.unit program world definitions⟩

theorem evaluate_bool_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store} {literal : Bool}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (_environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context (.bool literal) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store (.bool literal) =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  simp [infer] at inferredAt
  cases inferredAt
  have expectedEq : expected = .bool := by
    simpa [StaticType.erase] using resultType.symm
  subst expected
  cases fuel with
  | zero => simp [evaluate] at completed
  | succ remaining =>
      have completed' : RunResult.done (.bool literal) store =
          .done value finalStore := by
        simpa [evaluate] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping,
        Value.GraphHasType.bool program world literal definitions⟩

theorem evaluate_word_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store} {literal : Core.Word}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (_environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context (.word literal) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store (.word literal) =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  simp [infer] at inferredAt
  cases inferredAt
  have expectedEq : expected = .word := by
    simpa [StaticType.erase] using resultType.symm
  subst expected
  cases fuel with
  | zero => simp [evaluate] at completed
  | succ remaining =>
      have completed' : RunResult.done (.word literal) store =
          .done value finalStore := by
        simpa [evaluate] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping,
        Value.GraphHasType.word program world literal definitions⟩

/-- A successfully resolved global evaluates to a deeply typed finite-graph
reference, provided the entire table was genuinely checked. -/
theorem evaluate_global_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store} {key : Key}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (wellTyped : program.IsWellTyped)
    (_environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context (.global key) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store (.global key) =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨inferred, inferredAt, resultType⟩ := staticTyping
  cases signatureFound : program.findSignature? key with
  | none => simp [infer, signatureFound] at inferredAt
  | some signature =>
      simp [infer, signatureFound] at inferredAt
      cases inferredAt
      have expectedEq : expected = signature.toCoreType := by
        simpa [StaticType.erase, Signature.toCoreType] using resultType.symm
      subst expected
      cases fuel with
      | zero => simp [evaluate] at completed
      | succ remaining =>
          cases found : program.findDefinition? key with
          | none =>
              simp [Program.findSignature?, found] at signatureFound
          | some definition =>
              have completed' : RunResult.done (.global key) store =
                  .done value finalStore := by
                simpa [evaluate, found] using completed
              cases completed'
              exact ⟨world, .refl world, storeTyping,
                Value.GraphHasType.global wellTyped signatureFound⟩

/-- Evaluating a statically checked source lambda builds a deeply typed
closure with its checked body and deeply typed lexical capture. -/
theorem evaluate_lambda_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {parameters : List Parameter} {resultType : Core.Ty}
    {body : Expr} {expected : Core.Ty}
    {value : Value} {fuel : Nat}
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context
      (.lambda parameters resultType body) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate fuel program environment store
      (.lambda parameters resultType body) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨bodyTyping, expectedEq⟩ := staticTyping.lambda_body
  subst expected
  cases fuel with
  | zero => simp [evaluate] at completed
  | succ remaining =>
      have completed' : RunResult.done
          (.closure parameters resultType body environment) store =
          .done value finalStore := by
        simpa [evaluate] using completed
      cases completed'
      exact ⟨world, .refl world, storeTyping,
        Value.GraphHasType.sourceClosure environmentTyping bodyTyping⟩

/-- The actual `let` evaluator branch composes two recursive preservation
steps while carrying the heap-world extension and weakening the captured
environment between them. -/
theorem evaluate_let_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {binder : Resolved.LocalId} {boundExpression body : Expr}
    {inferred : StaticType} {expected : Core.Ty}
    {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (boundTyping : Expr.InfersType program context boundExpression
      inferred.erase)
    (bodyTyping : Expr.InfersType program ((binder, inferred) :: context)
      body expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.letE binder boundExpression body) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  cases boundRun : evaluate fuel program environment store boundExpression with
  | outOfFuel nextStore =>
      simp [evaluate, boundRun] at completed
  | fault error nextStore =>
      simp [evaluate, boundRun] at completed
  | done boundValue bodyStore =>
      obtain ⟨bodyWorld, firstExtension, bodyStoreTyping,
        boundValueTyping⟩ :=
        bodyPreservation environmentTyping boundTyping storeTyping boundRun
      have capturedTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      have extendedTyping : EnvironmentGraphHasTypes program bodyWorld
          ((binder, boundValue) :: environment)
          ((binder, inferred) :: context) definitions :=
        .cons boundValueTyping capturedTyping
      have bodyRun : evaluate fuel program
          ((binder, boundValue) :: environment) bodyStore body =
          .done value finalStore := by
        simpa [evaluate, boundRun] using completed
      obtain ⟨finalWorld, secondExtension, finalStoreTyping,
        resultTyping⟩ :=
        bodyPreservation extendedTyping bodyTyping bodyStoreTyping bodyRun
      exact ⟨finalWorld, firstExtension.trans secondExtension,
        finalStoreTyping, resultTyping⟩

/-- Pair evaluation preserves deep typing across its left-to-right store
threading, including heap references captured by the left component. -/
theorem evaluate_pair_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {left right : Expr} {leftType rightType : Core.Ty}
    {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (leftTyping : Expr.InfersType program context left leftType)
    (rightTyping : Expr.InfersType program context right rightType)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.pair left right) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value
        (.product leftType rightType) definitions := by
  cases leftRun : evaluate fuel program environment store left with
  | outOfFuel nextStore =>
      simp [evaluate, leftRun] at completed
  | fault error nextStore =>
      simp [evaluate, leftRun] at completed
  | done leftValue rightStore =>
      obtain ⟨middleWorld, firstExtension, rightStoreTyping,
        leftValueTyping⟩ :=
        bodyPreservation environmentTyping leftTyping storeTyping leftRun
      have nextEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      cases rightRun : evaluate fuel program environment rightStore right with
      | outOfFuel nextStore =>
          simp [evaluate, leftRun, rightRun] at completed
      | fault error nextStore =>
          simp [evaluate, leftRun, rightRun] at completed
      | done rightValue pairStore =>
          obtain ⟨finalWorld, secondExtension, pairStoreTyping,
            rightValueTyping⟩ :=
            bodyPreservation nextEnvironmentTyping rightTyping
              rightStoreTyping rightRun
          have completed' : RunResult.done (.pair leftValue rightValue)
              pairStore = .done value finalStore := by
            simpa [evaluate, leftRun, rightRun] using completed
          cases completed'
          exact ⟨finalWorld, firstExtension.trans secondExtension,
            pairStoreTyping,
            .pair (leftValueTyping.weaken secondExtension)
              rightValueTyping⟩

/-- The actual graph `apply` evaluator branch composes deep function
evaluation, ordered argument evaluation, structural argument bundling, and
the three typed application-dispatch branches. -/
theorem evaluate_apply_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {function : Expr} {arguments : List Expr}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (wellTyped : program.IsWellTyped)
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (staticTyping : Expr.InfersType program context
      (.apply function arguments) expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.apply function arguments) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  obtain ⟨functionType, argumentTypes, parameterType, resultType,
    functionInferred, argumentsInferred, functionErased, bundleEqual,
    resultEqual⟩ := staticTyping.apply_components
  have functionStatic : Expr.InfersType program context function
      (.function parameterType resultType) :=
    ⟨functionType, functionInferred, functionErased⟩
  have argumentsStatic := ExpressionsHaveTypes.ofInferList program context
    arguments argumentTypes argumentsInferred
  cases functionRun : evaluate fuel program environment store function with
  | outOfFuel nextStore =>
      simp [evaluate, functionRun] at completed
  | fault error nextStore =>
      simp [evaluate, functionRun] at completed
  | done functionValue argumentsStore =>
      obtain ⟨functionWorld, firstExtension, argumentsStoreTyping,
        functionValueTyping⟩ :=
        bodyPreservation environmentTyping functionStatic storeTyping
          functionRun
      have argumentsEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      cases argumentsRun : evaluateArguments
          (evaluate fuel program environment) argumentsStore arguments with
      | outOfFuel nextStore =>
          simp [evaluate, functionRun, argumentsRun] at completed
      | fault error nextStore =>
          simp [evaluate, functionRun, argumentsRun] at completed
      | done argumentValues callStore =>
          obtain ⟨argumentsWorld, secondExtension, callStoreTyping,
            argumentValuesTyping⟩ :=
            argumentsStatic.evaluateArguments_done_deep
              (evaluate fuel program) bodyPreservation
              argumentsEnvironmentTyping argumentsStoreTyping argumentsRun
          have callableTyping := functionValueTyping.weaken secondExtension
          have bundledTyping : Value.GraphHasType program argumentsWorld
              (packValues argumentValues) parameterType definitions := by
            simpa [bundleEqual] using argumentValuesTyping.packValues
          have applied : applyValue program (evaluate fuel program) fuel
              functionValue argumentValues callStore =
              .done value finalStore := by
            simpa [evaluate, functionRun, argumentsRun] using completed
          obtain ⟨finalWorld, thirdExtension, finalStoreTyping,
            resultTyping⟩ :=
            applyValue_done_deep (evaluate fuel program) bodyPreservation
              wellTyped callableTyping bundledTyping callStoreTyping applied
          exact ⟨finalWorld,
            firstExtension.trans (secondExtension.trans thirdExtension),
            finalStoreTyping, by simpa [resultEqual] using resultTyping⟩

/-- Unary evaluation preserves deep typing after a successful Core
projection and primitive operation. -/
theorem evaluate_unary_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {op : Core.UnaryOp} {operand : Expr}
    {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (operandTyping : Expr.InfersType program context operand op.operandType)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.unary op operand) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value op.resultType definitions := by
  cases operandRun : evaluate fuel program environment store operand with
  | outOfFuel nextStore =>
      simp [evaluate, operandRun] at completed
  | fault error nextStore =>
      simp [evaluate, operandRun] at completed
  | done operandValue operandStore =>
      obtain ⟨finalWorld, extension, finalStoreTyping,
        operandValueTyping⟩ :=
        bodyPreservation environmentTyping operandTyping storeTyping
          operandRun
      cases projected : operandValue.toCore? with
      | none =>
          simp [evaluate, operandRun, projected] at completed
      | some coreOperand =>
          have coreOperandTyping := operandValueTyping.toCore projected
          cases applied : op.apply coreOperand with
          | none =>
              simp [evaluate, operandRun, projected, applied] at completed
          | some coreResult =>
              have completed' : RunResult.done (Value.ofCore coreResult)
                  operandStore = .done value finalStore := by
                simpa [evaluate, operandRun, projected, applied] using
                  completed
              cases completed'
              exact ⟨finalWorld, extension, finalStoreTyping,
                unary_apply_result_graph_type applied⟩

/-- Binary evaluation preserves deep typing while threading the store and
heap-world extension through both operand evaluations. -/
theorem evaluate_binary_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {op : Core.BinaryOp} {left right : Expr}
    {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (leftTyping : Expr.InfersType program context left op.leftType)
    (rightTyping : Expr.InfersType program context right op.rightType)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.binary op left right) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value op.resultType definitions := by
  cases leftRun : evaluate fuel program environment store left with
  | outOfFuel nextStore =>
      simp [evaluate, leftRun] at completed
  | fault error nextStore =>
      simp [evaluate, leftRun] at completed
  | done leftValue rightStore =>
      obtain ⟨middleWorld, firstExtension, rightStoreTyping,
        leftValueTyping⟩ :=
        bodyPreservation environmentTyping leftTyping storeTyping leftRun
      have nextEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      cases rightRun : evaluate fuel program environment rightStore right with
      | outOfFuel nextStore =>
          simp [evaluate, leftRun, rightRun] at completed
      | fault error nextStore =>
          simp [evaluate, leftRun, rightRun] at completed
      | done rightValue binaryStore =>
          obtain ⟨finalWorld, secondExtension, binaryStoreTyping,
            rightValueTyping⟩ :=
            bodyPreservation nextEnvironmentTyping rightTyping
              rightStoreTyping rightRun
          cases leftProjection : leftValue.toCore? with
          | none =>
              simp [evaluate, leftRun, rightRun, leftProjection] at completed
          | some coreLeft =>
              have coreLeftTyping :=
                (leftValueTyping.weaken secondExtension).toCore leftProjection
              cases rightProjection : rightValue.toCore? with
              | none =>
                  simp [evaluate, leftRun, rightRun, leftProjection,
                    rightProjection] at completed
              | some coreRight =>
                  have coreRightTyping := rightValueTyping.toCore rightProjection
                  cases applied : op.apply coreLeft coreRight with
                  | none =>
                      simp [evaluate, leftRun, rightRun, leftProjection,
                        rightProjection, applied] at completed
                  | some coreResult =>
                      have completed' : RunResult.done (Value.ofCore coreResult)
                          binaryStore = .done value finalStore := by
                        simpa [evaluate, leftRun, rightRun, leftProjection,
                          rightProjection, applied] using completed
                      cases completed'
                      exact ⟨finalWorld,
                        firstExtension.trans secondExtension,
                        binaryStoreTyping,
                        binary_apply_result_graph_type applied⟩

/-- The word-comparison branch preserves the deep result and the sequential
store invariant. -/
theorem evaluate_wordLt_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {left right : Expr} {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (leftTyping : Expr.InfersType program context left .word)
    (rightTyping : Expr.InfersType program context right .word)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.wordLt left right) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value .bool definitions := by
  cases leftRun : evaluate fuel program environment store left with
  | outOfFuel nextStore =>
      simp [evaluate, leftRun] at completed
  | fault error nextStore =>
      simp [evaluate, leftRun] at completed
  | done leftValue rightStore =>
      obtain ⟨middleWorld, firstExtension, rightStoreTyping,
        leftValueTyping⟩ :=
        bodyPreservation environmentTyping leftTyping storeTyping leftRun
      have nextEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken firstExtension environmentTyping
      cases leftValue with
      | word leftWord =>
          cases rightRun : evaluate fuel program environment rightStore right with
          | outOfFuel nextStore =>
              simp [evaluate, leftRun, rightRun] at completed
          | fault error nextStore =>
              simp [evaluate, leftRun, rightRun] at completed
          | done rightValue comparisonStore =>
              obtain ⟨finalWorld, secondExtension,
                comparisonStoreTyping, rightValueTyping⟩ :=
                bodyPreservation nextEnvironmentTyping rightTyping
                  rightStoreTyping rightRun
              cases rightValue with
              | word rightWord =>
                  have completed' : RunResult.done
                      (.bool (decide (leftWord < rightWord)))
                      comparisonStore = .done value finalStore := by
                    simpa [evaluate, leftRun, rightRun] using completed
                  cases completed'
                  exact ⟨finalWorld, firstExtension.trans secondExtension,
                    comparisonStoreTyping,
                    Value.GraphHasType.bool program finalWorld _ definitions⟩
              | _ => simp [evaluate, leftRun, rightRun] at completed
      | _ => simp [evaluate, leftRun] at completed

/-- A well-typed conditional selects a well-typed branch, preserving the
store/world invariant established while evaluating its condition. -/
theorem evaluate_ifE_done_deep
    {program : Program} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    {environment : Environment} {context : StaticContext}
    {store finalStore : Core.Store}
    {condition thenBranch elseBranch : Expr}
    {expected : Core.Ty} {value : Value} {fuel : Nat}
    (bodyPreservation : BodyPreservesGraphTyping program
      (evaluate fuel program))
    (environmentTyping : EnvironmentGraphHasTypes program world
      environment context definitions)
    (conditionTyping : Expr.InfersType program context condition .bool)
    (thenTyping : Expr.InfersType program context thenBranch expected)
    (elseTyping : Expr.InfersType program context elseBranch expected)
    (storeTyping : Core.StoreHasTypes world store)
    (completed : evaluate (fuel + 1) program environment store
      (.ifE condition thenBranch elseBranch) = .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType program finalWorld value expected definitions := by
  cases conditionRun : evaluate fuel program environment store condition with
  | outOfFuel nextStore =>
      simp [evaluate, conditionRun] at completed
  | fault error nextStore =>
      simp [evaluate, conditionRun] at completed
  | done conditionValue branchStore =>
      obtain ⟨branchWorld, extension, branchStoreTyping,
        conditionValueTyping⟩ :=
        bodyPreservation environmentTyping conditionTyping storeTyping
          conditionRun
      have branchEnvironmentTyping :=
        EnvironmentGraphHasTypes.weaken extension environmentTyping
      cases conditionValue with
      | bool selected =>
          cases selected with
          | false =>
              have branchRun : evaluate fuel program environment branchStore
                  elseBranch = .done value finalStore := by
                simpa [evaluate, conditionRun] using completed
              obtain ⟨finalWorld, secondExtension, finalStoreTyping,
                resultTyping⟩ :=
                bodyPreservation branchEnvironmentTyping elseTyping
                  branchStoreTyping branchRun
              exact ⟨finalWorld, extension.trans secondExtension,
                finalStoreTyping, resultTyping⟩
          | true =>
              have branchRun : evaluate fuel program environment branchStore
                  thenBranch = .done value finalStore := by
                simpa [evaluate, conditionRun] using completed
              obtain ⟨finalWorld, secondExtension, finalStoreTyping,
                resultTyping⟩ :=
                bodyPreservation branchEnvironmentTyping thenTyping
                  branchStoreTyping branchRun
              exact ⟨finalWorld, extension.trans secondExtension,
                finalStoreTyping, resultTyping⟩
      | _ => simp [evaluate, conditionRun] at completed


end Solcore.Frontend.SourceRuntime
