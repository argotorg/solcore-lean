import Solcore.Frontend.LocalFragmentProperties
import Solcore.Frontend.RuntimeFunctionCompilationProperties
import Solcore.Frontend.RuntimeFunctionEntryProperties

/-! Only exact whole-entry provenance constrains a retained Core expression.
Compiled/prepared records and same-type replacements alone are not evidence.
The structural conclusion imposes no restriction on actual argument values. -/
set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionCompiles.localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    Core.Expr.LocalFragment compiled.core :=
  compilation.body.localFragment

theorem RuntimeFunctionPrepares.localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    Core.Expr.LocalFragment prepared.core :=
  preparation.body.localFragment

theorem compileRuntimeFunction?_localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (accepted : compileRuntimeFunction? types owner declaration = some compiled) :
    Core.Expr.LocalFragment compiled.core :=
  (compileRuntimeFunction?_sound accepted).localFragment

theorem prepareRuntimeFunction?_localFragment
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (accepted : prepareRuntimeFunction? types owner declaration arguments = some prepared) :
    Core.Expr.LocalFragment prepared.core :=
  (prepareRuntimeFunction?_sound accepted).localFragment

end Solcore.Frontend
