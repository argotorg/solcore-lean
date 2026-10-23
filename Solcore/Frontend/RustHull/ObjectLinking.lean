import Solcore.Frontend.RustHull.CodeImage
import Solcore.Frontend.RustHull.LoweringSupport

/-! Resolve object symbols before lowering Yul string literals to EVM words.
Symbol names are arbitrary strings and belong to a section-local namespace.
Lexical Yul functions can shadow intrinsic names. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.ObjectLinking

private def decodeChars : List Char → Option (List Char)
  | [] => some []
  | '\\' :: escaped :: rest => do
      let char ← match escaped with
        | '"' => some '"' | '\\' => some '\\' | 'n' => some '\n' | 't' => some '\t'
        | _ => none
      return char :: (← decodeChars rest)
  | '\\' :: [] | '"' :: _ => none
  | char :: rest => return char :: (← decodeChars rest)

private def symbolText (expression : YulExpr) : LowerM String := do
  let .literal (.string text) := expression.kind | fail "object symbol must be a string literal" expression.span
  let '"' :: rest := text.toList | fail "object symbol is missing its opening quote" expression.span
  let '"' :: inner := rest.reverse | fail "object symbol is missing its closing quote" expression.span
  match decodeChars inner.reverse with
  | some chars => pure (String.ofList chars)
  | none => fail "invalid object symbol string" expression.span

private def expression : Nat → CodeImage.Image → List String → YulExpr → LowerM YulExpr
  | 0, _, _, value => fail "object symbol expression depth exhausted" value.span
  | fuel + 1, image, functions, value => do
      match value.kind with
      | .call name args =>
          if (name.name = "datasize" || name.name = "dataoffset") && !functions.contains name.name then
            let [argument] := args | fail "object symbol intrinsic requires one argument" value.span
            let symbol ← symbolText argument
            let extent ← (CodeImage.resolve image symbol).mapError fun message => ⟨message, value.span⟩
            let number := if name.name = "datasize" then extent.size else extent.offset
            pure {value with kind := .literal (.number (toString number))}
          else
            return {value with kind := .call name (← args.mapM (expression fuel image functions))}
      | _ => pure value

private def yulStatements : Nat → CodeImage.Image → List String → List YulStmt → LowerM (List YulStmt)
  | 0, _, _, _ => fail "object symbol Yul statement depth exhausted"
  | fuel + 1, image, functions, body => do
      let functions := (body.filterMap fun statement => match statement.kind with
        | .functionDef name _ _ _ => some name.name
        | _ => none) ++ functions
      body.mapM fun statement => do
        let kind : YulStmtKind ← match statement.kind with
          | .block body => YulStmtKind.block <$> yulStatements fuel image functions body
          | .letDecl names init => YulStmtKind.letDecl names <$> init.mapM (expression fuel image functions)
          | .assign names value => YulStmtKind.assign names <$> expression fuel image functions value
          | .expression value => YulStmtKind.expression <$> expression fuel image functions value
          | .ifThen cond body => do
              let cond ← expression fuel image functions cond
              let body ← yulStatements fuel image functions body
              pure (.ifThen cond body)
          | .forLoop init cond post body => do
              -- Initializer functions remain visible throughout the loop.
              let loopFunctions := (init.filterMap fun statement => match statement.kind with
                | .functionDef name _ _ _ => some name.name
                | _ => none) ++ functions
              let init ← yulStatements fuel image functions init
              let cond ← expression fuel image loopFunctions cond
              let post ← yulStatements fuel image loopFunctions post
              let body ← yulStatements fuel image loopFunctions body
              pure (.forLoop init cond post body)
          | .switch value cases defaultBody => do
              let cases ← cases.mapM fun arm => do
                let body ← yulStatements fuel image functions arm.body
                pure {arm with body}
              let value ← expression fuel image functions value
              let defaultBody ← defaultBody.mapM (yulStatements fuel image functions)
              pure (.switch value cases defaultBody)
          | .functionDef name params rets body =>
              YulStmtKind.functionDef name params rets <$> yulStatements fuel image functions body
          | .leave => pure .leave
          | .breakStmt => pure .breakStmt
          | .continueStmt => pure .continueStmt
        pure {statement with kind}

private def statements : Nat → CodeImage.Image → List Stmt → LowerM (List Stmt)
  | 0, _, _ => fail "object symbol Hull statement depth exhausted"
  | fuel + 1, image, body => body.mapM fun statement => do
      let kind : StmtKind ← match statement.kind with
        | .assembly body => StmtKind.assembly <$> yulStatements fuel image [] body
        | .block body => StmtKind.block <$> statements fuel image body
        | .forLoop init cond post body => do
            let init ← statements fuel image init
            let post ← statements fuel image post
            let body ← statements fuel image body
            pure (.forLoop init cond post body)
        | .matchStmt target scrutinee alts => do
            let alts ← alts.mapM fun arm => do
              let body ← statements fuel image arm.body
              pure {arm with body}
            pure (.matchStmt target scrutinee alts)
        | other => pure other
      pure {statement with kind}

private def function (fuel : Nat) (image : CodeImage.Image) (value : Function) : LowerM Function := do
  return {value with body := (← statements fuel image value.body)}

private def objects : Nat → CodeImage.Image → List String → List Object → LowerM (List Object)
  | 0, _, _, _ => fail "object symbol path depth exhausted"
  | fuel + 1, image, path, values => values.mapM fun value => do
      let .object name code children span := value
      match path with
      | [] => fail "object symbol path must not be empty"
      | current :: rest =>
          if current != name then pure value
          else if rest.isEmpty then do
            let stmts ← statements fuel image code.stmts
            let functions ← code.functions.mapM (function fuel image)
            let code := {code with stmts, functions}
            pure (.object name code children span)
          else
            return .object name code (← objects fuel image rest children) span

/-- Resolve the selected section and its shared functions. Validate the complete
image inventory before calling this function; other object sections keep their
own symbol namespaces and remain unchanged. -/
def link (program : Program) (image : CodeImage.Image) (fuel : Nat := 4096) : LowerM Program := do
  let functions ← program.functions.mapM (function fuel image)
  let objects ← objects fuel image image.path program.objects
  return {program with functions, objects}

end Solcore.Frontend.RustHull.ObjectLinking
