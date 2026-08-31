import Solcore.Syntax.Parser.FileItemStrictProperties

namespace Tests
open Solcore.Syntax.Parser
example := @importDecl_cursor_lt_onSuccess
example := @exportDecl_cursor_lt_onSuccess
example := @typeAlias_cursor_lt_onSuccess
example := @functionDecl_cursor_lt_onSuccess
example := @enumDecl_cursor_lt_onSuccess
example := @FileInternals.plainTopItem_cursor_lt_onSuccess
example := @FileInternals.parseItemsItem_cursor_lt_onSuccess
end Tests
