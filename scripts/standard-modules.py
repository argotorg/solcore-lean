#!/usr/bin/env python3
"""Upstream's standard modules as Lean's whole-program load knows them.

Reads `std` at the pinned upstream commit from the retained checkout (through `git show`, so the
exporter's patches to its working tree do not matter): each module's path, the names it exports
and their namespaces (function, type or trait; constructors are no import items), the functions
`std.opcodes` exports, the exports that another std module declares, with that module and the
item's name there (upstream's `SC0111` compares exports by these origins), and the constructors
each exported type shows (upstream's `SC0114` and `SC0115` check selections against them). It
writes `Solcore/Frontend/StandardModules.lean` (`--write`) or checks that file against the
checkout (`--check`, the default). After a re-pin, `--write` regenerates the file.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
COMMIT = "d1b5ac28c0a5821c1a56758f182e27bc5e7c4f09"
UPSTREAM = ROOT / ".upstream/solcore-rs-20261116"
TARGET = ROOT / "Solcore/Frontend/StandardModules.lean"
OPCODES = "std.opcodes"
NAMESPACES = {"function": "function", "enum": "type", "struct": "type", "type": "type", "contract": "type",
              "trait": "trait"}

DECLARATION = re.compile(r"\b(function|enum|struct|type|contract|trait)\s+([A-Za-z_]\w*)")
ENUM = re.compile(r"\benum\s+([A-Za-z_]\w*)")
STATEMENT = re.compile(r"\b(import|export)\b([^;]*);")
IDENTIFIER = re.compile(r"[A-Za-z_]\w*")
MODULE = r"[A-Za-z_]\w*(?:\s*\.\s*[A-Za-z_]\w*)*"


class StandardError(ValueError):
    """A standard module this script cannot read; a re-pin that adds a form it does not know fails here."""


def strip(text: str) -> str:
    """The source with comments and string literals blanked, so braces and keywords inside them do not count."""
    def blank(match: re.Match) -> str:
        return re.sub(r"[^\n]", " ", match.group(0))
    return re.sub(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"', blank, text, flags=re.S)


def depths(text: str) -> list[int]:
    """Each character's brace depth."""
    result, depth = [], 0
    for character in text:
        if character == "}":
            depth -= 1
        result.append(depth)
        if character == "{":
            depth += 1
    if depth != 0:
        raise StandardError("unbalanced braces")
    return result


def module_name(path: str) -> str:
    """The module a file of `std` is: `std/std.sol` is `std`, `std/a/b.sol` is `std.a.b`."""
    parts = path[:-len(".sol")].split("/")
    if parts == ["std", "std"]:
        return "std"
    return ".".join(parts)


def dotted(text: str) -> str:
    return ".".join(part.strip() for part in text.split("."))


def entries(body: str) -> list[str]:
    """A list's entries, split at the commas outside parentheses, brackets, braces and angles."""
    parts, depth, current = [], 0, []
    for character in body:
        if character in "([{<":
            depth += 1
        elif character in ")]}>":
            depth -= 1
        if character == "," and depth == 0:
            parts.append("".join(current))
            current = []
        else:
            current.append(character)
    parts.append("".join(current))
    return [part.strip() for part in parts if part.strip()]


def selections(text: str) -> list[tuple[str, str | list[str] | None]]:
    """A braced item list's names, each with its constructor selection: `*`, the constructors named,
    or `None` for a name without one."""
    body = text.strip()
    if not (body.startswith("{") and body.endswith("}")):
        raise StandardError(f"not an item list: {text.strip()[:60]}")
    result: list[tuple[str, str | list[str] | None]] = []
    for item in entries(body[1:-1]):
        found = re.fullmatch(r"([A-Za-z_]\w*)\s*(?:\(([^)]*)\))?", item)
        if not found:
            raise StandardError(f"an export item this script does not read: {item}")
        selection = found.group(2)
        if selection is None:
            result.append((found.group(1), None))
        elif selection.strip() == "*":
            result.append((found.group(1), "*"))
        else:
            result.append((found.group(1), [name.strip() for name in selection.split(",") if name.strip()]))
    return result


def items(text: str) -> list[str]:
    """The names of a braced item list, each without its constructor selection (`T(*)`, `T(A, B)`)."""
    body = text.strip()
    if not (body.startswith("{") and body.endswith("}")):
        raise StandardError(f"not an item list: {text.strip()[:60]}")
    names = []
    for item in re.sub(r"\([^)]*\)", "", body[1:-1]).split(","):
        item = item.strip()
        if item:
            if not IDENTIFIER.fullmatch(item):
                raise StandardError(f"an export item this script does not read: {item}")
            names.append(item)
    return names


class Module:
    def __init__(self, name: str, source: str):
        self.name = name
        text = strip(source)
        depth = depths(text)
        self.declarations: dict[str, list[str]] = {}
        for match in DECLARATION.finditer(text):
            if depth[match.start()] == 0:
                namespace = NAMESPACES[match.group(1)]
                found = self.declarations.setdefault(match.group(2), [])
                if namespace not in found:
                    found.append(namespace)
        self.constructors: dict[str, list[str]] = {}
        for match in ENUM.finditer(text):
            if depth[match.start()] == 0:
                start = text.index("{", match.end())
                end, level = start + 1, 1
                while level:
                    level += {"{": 1, "}": -1}.get(text[end], 0)
                    end += 1
                found = []
                for entry in entries(text[start + 1:end - 1]):
                    constructor = IDENTIFIER.match(entry)
                    if not constructor:
                        raise StandardError(f"a constructor this script does not read in {name}: {entry[:40]}")
                    found.append(constructor.group(0))
                self.constructors[match.group(1)] = found
        self.imports, self.exports = [], []
        for match in STATEMENT.finditer(text):
            if depth[match.start()] == 0:
                body = " ".join(match.group(2).split())
                (self.imports if match.group(1) == "import" else self.exports).append(body)


def selection_of(body: str) -> tuple[str, list[str], list[str]] | None:
    """An import's module, the names it brings (`*` for all) as `source:local` pairs, and the hidden names."""
    hidden = []
    hiding = re.search(r"\bhiding\s*(\{[^}]*\})\s*$", body)
    if hiding:
        hidden = items(hiding.group(1))
        body = body[:hiding.start()].strip()
    wildcard = re.fullmatch(rf"\*\s*from\s+({MODULE})", body)
    if wildcard:
        return dotted(wildcard.group(1)), ["*"], hidden
    selected = re.fullmatch(rf"(\{{[^}}]*\}})\s*from\s+({MODULE})", body)
    if selected:
        pairs = []
        for item in selected.group(1)[1:-1].split(","):
            item = item.strip()
            if not item:
                continue
            alias = re.fullmatch(r"([A-Za-z_]\w*)\s+as\s+([A-Za-z_]\w*)", item)
            if alias:
                pairs.append(f"{alias.group(1)}:{alias.group(2)}")
            elif IDENTIFIER.fullmatch(item):
                pairs.append(f"{item}:{item}")
            else:
                raise StandardError(f"an import item this script does not read: {item}")
        return dotted(selected.group(2)), pairs, hidden
    plain = re.fullmatch(rf"{MODULE}(?:\s+as\s+[A-Za-z_]\w*)?", body)
    if plain or re.fullmatch(rf"\*\s*as\s+\w+\s+from\s+{MODULE}", body):
        return None  # a plain or namespace import binds no unqualified name
    raise StandardError(f"an import this script does not read: {body}")


class Library:
    def __init__(self, sources: dict[str, str]):
        self.modules = {module_name(path): Module(module_name(path), text) for path, text in sources.items()}
        self.memo: dict[str, list[tuple[str, str]]] = {}
        self.active: set[str] = set()
        self.detail_memo: dict[str, dict[str, tuple[str, str, list[str]]]] = {}

    def module(self, name: str) -> Module:
        if name not in self.modules:
            raise StandardError(f"no standard module {name}")
        return self.modules[name]

    def named(self, module: str, name: str) -> list[tuple[str, str]]:
        return [entry for entry in self.exports(module) if entry[0] == name]

    def imported(self, module: Module, name: str) -> list[tuple[str, str]]:
        """The namespaces of a name the module imports and exports again."""
        found = []
        for body in module.imports:
            selection = selection_of(body)
            if selection is None:
                continue
            target, pairs, hidden = selection
            if not target.startswith("std"):
                continue
            if pairs == ["*"]:
                if name not in hidden:
                    found += [(name, namespace) for _, namespace in self.named(target, name)]
            else:
                for pair in pairs:
                    source, local = pair.split(":")
                    if local == name:
                        found += [(name, namespace) for _, namespace in self.named(target, source)]
        return found

    def exports(self, name: str) -> list[tuple[str, str]]:
        """The module's exports, each name with its namespace, in export order."""
        if name in self.memo:
            return self.memo[name]
        if name in self.active:
            raise StandardError(f"an export cycle through {name}")
        self.active.add(name)
        module = self.module(name)
        result: list[tuple[str, str]] = []
        for body in module.exports:
            reexport = re.fullmatch(rf"({MODULE})\s*\.\s*(\{{[^}}]*\}}|\*)", body)
            if body.startswith("{"):
                for item in items(body):
                    entries = [(item, namespace) for namespace in module.declarations.get(item, [])]
                    entries = entries or self.imported(module, item)
                    if not entries:
                        raise StandardError(f"{name} exports {item}, which it neither declares nor imports")
                    result += entries
            elif reexport:
                source = dotted(reexport.group(1))
                if reexport.group(2) == "*":
                    result += self.exports(source)
                else:
                    for item in items(reexport.group(2)):
                        entries = self.named(source, item)
                        if not entries:
                            raise StandardError(f"{name} exports {item} from {source}, which does not export it")
                        result += entries
            else:
                raise StandardError(f"an export this script does not read in {name}: {body}")
        unique = []
        for entry in result:
            if entry not in unique:
                unique.append(entry)
        self.active.discard(name)
        self.memo[name] = unique
        return unique


    def shown(self, constructors: list[str], selection: str | list[str] | None, owner: str, item: str) -> list[str]:
        """The constructors an export with this selection shows of a type that shows these."""
        if selection == "*":
            return constructors
        if selection is None:
            return []
        missing = [name for name in selection if name not in constructors]
        if missing:
            raise StandardError(f"{owner} exports {item}({', '.join(missing)}), which it does not show")
        return [name for name in constructors if name in selection]

    def imported_detail(self, module: Module, name: str) -> tuple[str, str, list[str]] | None:
        """The std item a name the module imports is, with the constructors its source shows."""
        for body in module.imports:
            selection = selection_of(body)
            if selection is None:
                continue
            target, pairs, hidden = selection
            if not target.startswith("std"):
                continue
            if pairs == ["*"]:
                if name not in hidden and name in self.details(target):
                    return self.details(target)[name]
            else:
                for pair in pairs:
                    source, local = pair.split(":")
                    if local == name and source in self.details(target):
                        return self.details(target)[source]
        return None

    def details(self, name: str) -> dict[str, tuple[str, str, list[str]]]:
        """Each export of the module, by its name, with the std item it is (the module that declares
        it and the item's name there) and, for a type, the constructors the export shows: a type's
        own for `T(*)`, those named, or none."""
        if name in self.detail_memo:
            return self.detail_memo[name]
        self.exports(name)  # the forms are read, and cycles refused, there
        module = self.module(name)
        result: dict[str, tuple[str, str, list[str]]] = {}
        for body in module.exports:
            reexport = re.fullmatch(rf"({MODULE})\s*\.\s*(\{{[^}}]*\}}|\*)", body)
            if body.startswith("{"):
                for item, selection in selections(body):
                    if item in module.declarations:
                        own = module.constructors.get(item, [])
                        result.setdefault(item, (name, item, self.shown(own, selection, name, item)))
                    else:
                        origin = self.imported_detail(module, item)
                        if origin is None:
                            raise StandardError(f"{name} exports {item}, which it neither declares nor imports")
                        result.setdefault(item, (origin[0], origin[1], self.shown(origin[2], selection, name, item)))
            elif reexport:
                source = self.details(dotted(reexport.group(1)))
                if reexport.group(2) == "*":
                    for item, detail in source.items():
                        result.setdefault(item, detail)
                else:
                    for item, selection in selections(reexport.group(2)):
                        origin = source[item]
                        result.setdefault(item, (origin[0], origin[1], self.shown(origin[2], selection, name, item)))
        self.detail_memo[name] = result
        return result


def read_checkout(upstream: Path) -> dict[str, str]:
    def git(*args: str) -> str:
        return subprocess.check_output(["git", "-C", str(upstream), *args], text=True)
    paths = [path for path in git("ls-tree", "-r", "--name-only", COMMIT, "std").splitlines()
             if path.endswith(".sol")]
    return {path: git("show", f"{COMMIT}:{path}") for path in sorted(paths)}


def lean_string_list(names: list[str], indent: str) -> str:
    lines, line = [], indent
    for index, name in enumerate(names):
        piece = f'"{name}"' + ("," if index + 1 < len(names) else "")
        if len(line) + len(piece) + 1 > 100 and line.strip():
            lines.append(line.rstrip())
            line = indent
        line += piece + " "
    lines.append(line.rstrip())
    return "\n".join(lines)


def path_list(name: str) -> str:
    """A module's path components as a Lean list of strings."""
    return "[" + ", ".join(f'"{part}"' for part in name.split(".")) + "]"


def wrapped(pieces: list[str], indent: str, tail: str) -> list[str]:
    """Pieces joined by commas, each line within 100 characters, the last piece followed by `tail`."""
    lines, line = [], indent
    for index, piece in enumerate(pieces):
        piece += tail if index + 1 == len(pieces) else ","
        if len(line) + len(piece) > 100 and line.strip():
            lines.append(line.rstrip())
            line = indent
        line += piece + " "
    lines.append(line.rstrip())
    return lines


def lean_list(names: list[str]) -> str:
    return "[" + ", ".join(f'"{name}"' for name in names) + "]"


def table(rows: list[tuple[str, list[str]]]) -> list[str]:
    """A Lean list of modules, each with its rendered entries, or the empty list."""
    if not rows:
        return ["  []"]
    out = ["["]
    for position, (name, pieces) in enumerate(rows):
        out.append(f"  ({path_list(name)}, [")
        out += wrapped(pieces, "      ", "])" + ("," if position + 1 < len(rows) else "]"))
    return out


def render(sources: dict[str, str]) -> str:
    library = Library(sources)
    opcodes = library.exports(OPCODES)
    if any(namespace != "function" for _, namespace in opcodes):
        raise StandardError("std.opcodes exports something other than a function")
    others = sorted(name for name in library.modules if name != OPCODES)
    paths = sorted(library.modules, key=lambda name: name.split("."))
    out = ["/-!",
           "# Upstream's standard modules",
           "",
           f"The modules of upstream's `std` at `{COMMIT[:8]}`, the names each exports with its",
           "namespace, and the functions `std.opcodes` exports. Generated by",
           "`scripts/standard-modules.py` from the pinned checkout: do not edit. The script's `--check`",
           "compares this file with the checkout, and `--write` regenerates it after a re-pin.",
           "-/",
           "",
           "set_option autoImplicit false",
           "",
           "namespace Solcore.Frontend",
           "",
           "/-- The namespace of a name that a standard module exports. Constructors are no import items:",
           "they are reached through their type. -/",
           "inductive StandardExportNamespace where",
           "  | function",
           "  | type",
           "  | trait",
           "  deriving Repr, BEq, DecidableEq",
           "",
           "/-- The upstream commit these tables are read from. -/",
           f'def upstreamStandardCommit : String := "{COMMIT}"',
           "",
           "/-- The modules of upstream's `std`, by path components. -/",
           "def upstreamStandardModulePaths : List (List String) :=",
           "  [" + ",\n    ".join(path_list(name) for name in paths) + "]",
           "",
           "/-- The functions upstream's `std.opcodes` exports, in its order: the 26 pure word functions,",
           "which are builtins (`WordOpcode`), and the others, which read or change memory, storage,",
           "the environment or control flow, and which Lean refuses where they are used. -/",
           "def standardOpcodeNames : List String :=",
           "  [" + lean_string_list([name for name, _ in opcodes], "    ").lstrip() + "]",
           "",
           "/-- Each module of upstream's `std` other than `std.opcodes`, by path components, with the names",
           "it exports and their namespaces, in its export order. A re-export is the module's own export. -/",
           "def upstreamStandardModuleExports :",
           "    List (List String × List (String × StandardExportNamespace)) := ["]
    for position, name in enumerate(others):
        path = path_list(name)
        entries = library.exports(name)
        rendered = [f'("{item}", .{namespace})' for item, namespace in entries]
        tail = "])" + ("," if position + 1 < len(others) else "]")
        lines, line = [], "      "
        for index, piece in enumerate(rendered):
            last = index + 1 == len(rendered)
            piece += tail if last else ","
            if len(line) + len(piece) > 100 and line.strip():
                lines.append(line.rstrip())
                line = "      "
            line += piece + " "
        lines.append(line.rstrip())
        out.append(f"  ({path}, [")
        out += lines
    origins, constructors = [], []
    for name in sorted(library.modules):
        details = library.details(name)
        moved = [f'("{item}", {path_list(module)}, "{source}")' for item, (module, source, _) in details.items()
                 if (module, source) != (name, item)]
        if moved:
            origins.append((name, moved))
        shown = [f'("{item}", {lean_list(names)})' for item, (_, _, names) in details.items() if names]
        if shown:
            constructors.append((name, shown))
    out += ["",
            "/-- Each std module's exports that another std module declares, by path components: the name,",
            "that module and the item's name there. Any other export is the module's own declaration of the",
            "name. Upstream's `SC0111` compares exports by these origins. -/",
            "def upstreamStandardExportOrigins :",
            "    List (List String × List (String × List String × String)) :="]
    rendered = table(origins)
    out += [out.pop() + " " + rendered[0]] + rendered[1:] if rendered[0] == "[" else rendered
    out += ["",
            "/-- Each std module's exported types that show constructors, with the constructors they show: a",
            "type exported as `T(*)` shows all of its own. Any other exported type shows none, as an opaque",
            "type does. -/",
            "def upstreamStandardExportConstructors :",
            "    List (List String × List (String × List String)) :="]
    rendered = table(constructors)
    out += [out.pop() + " " + rendered[0]] + rendered[1:] if rendered[0] == "[" else rendered
    out += ["", "end Solcore.Frontend", ""]
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--upstream", type=Path, default=UPSTREAM)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="write the Lean file from the checkout")
    mode.add_argument("--check", action="store_true", help="check the Lean file against the checkout (the default)")
    args = parser.parse_args(argv)
    try:
        expected = render(read_checkout(args.upstream))
    except (subprocess.CalledProcessError, FileNotFoundError) as error:
        print(f"cannot read std at {COMMIT[:8]} from {args.upstream}: {error}", file=sys.stderr)
        return 2
    except StandardError as error:
        print(f"std at {COMMIT[:8]}: {error}", file=sys.stderr)
        return 2
    if args.write:
        TARGET.write_text(expected)
        print(f"wrote {TARGET.relative_to(ROOT)} from std at {COMMIT[:8]}")
        return 0
    if not TARGET.exists() or TARGET.read_text() != expected:
        print(f"{TARGET.relative_to(ROOT)} differs from std at {COMMIT[:8]}; run with --write", file=sys.stderr)
        return 1
    print(f"{TARGET.relative_to(ROOT)} matches std at {COMMIT[:8]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
