#!/usr/bin/env python3
"""Check the layer discipline of AsmPhys (see README.md).

- AsmPhys/Spec: definitions only; imports only Mathlib and AsmPhys.Spec.
- AsmPhys/Design: definitions only; imports only Mathlib, AsmPhys.Spec and AsmPhys.Design.
- AsmPhys/Claims.lean: only imports, namespaces, sections, `open`, `variable` and theorems.
- Everywhere: nothing that changes how later source text elaborates (notation, macros, syntax,
  elaborators, instances, attributes other than those in ALLOWED_ATTRIBUTES, `export`,
  `#eval`-style commands), and no sorry, admit, axiom, opaque, unsafe or native_decide; bv_decide
  only in BV_DECIDE_ALLOWED.
- Every library file is imported by AsmPhys.lean, so `lake build` checks all of it.

What the claims say, and the imports of the compiled modules, are checked by scripts/Audit.lean.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = ROOT / "AsmPhys"
CLAIMS = "AsmPhys/Claims.lean"

# Bit-level datapath lemmas that may use bv_decide (handoff working rule); none yet.
BV_DECIDE_ALLOWED: set[str] = set()

# Attributes that only register lemmas with a tactic and cannot change how a statement elaborates.
ALLOWED_ATTRIBUTES = {"simp"}

LAYERS = {
    "Spec": ("Mathlib.", "AsmPhys.Spec."),
    "Design": ("Mathlib.", "AsmPhys.Spec.", "AsmPhys.Design."),
}

IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)", re.M)

# Anywhere in the library.
SYNTAX_CHANGING = re.compile(
    r"\b(notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|"
    r"declare_syntax_cat|initialize|builtin_initialize|instance|attribute|export|"
    r"unif_hint|run_cmd|run_elab|run_meta|opaque|unsafe|implemented_by|extern)\b"
    r"|#[a-z_]+\b"
)
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*axiom\b", re.M)
BV_DECIDE = re.compile(r"\bbv_decide\b")
ATTRIBUTE = re.compile(r"@\[([^\]]*)\]")

# Additionally in Spec and Design.
NOT_A_DEFINITION = re.compile(
    r"\b(theorem|lemma|example|axiom|set_option|partial|local)\b|@\["
)

# Top-level commands allowed in Claims.lean.
CLAIMS_COMMANDS = re.compile(r"^(import|namespace|end|section|open|variable|theorem)\b")


def strip_comments(text: str) -> str:
    """Remove block comments (including doc comments, which may nest) and line comments,
    keeping line breaks."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def strip_strings(code: str) -> str:
    return re.sub(r'"(\\.|[^"\\])*"', '""', code)


def line_of(code: str, pos: int) -> int:
    return code[:pos].count("\n") + 1


def main() -> int:
    errors = []
    files = sorted(LIB.rglob("*.lean"))
    root_code = strip_comments((ROOT / "AsmPhys.lean").read_text())
    root_imports = set(IMPORT.findall(root_code))
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        module = rel[: -len(".lean")].replace("/", ".")
        code = strip_strings(strip_comments(path.read_text()))
        if module not in root_imports:
            errors.append(f"{rel}: not imported by AsmPhys.lean")
        for m in FORBIDDEN.finditer(code):
            errors.append(f"{rel}:{line_of(code, m.start())}: `{m.group(0).strip()}`")
        for m in SYNTAX_CHANGING.finditer(code):
            errors.append(f"{rel}:{line_of(code, m.start())}: `{m.group(0)}` is not allowed")
        for m in ATTRIBUTE.finditer(code):
            attrs = {a.strip() for a in m.group(1).split(",")}
            if not attrs <= ALLOWED_ATTRIBUTES:
                errors.append(f"{rel}:{line_of(code, m.start())}: attribute `{m.group(0)}`")
        if BV_DECIDE.search(code) and rel not in BV_DECIDE_ALLOWED:
            errors.append(f"{rel}: uses bv_decide outside BV_DECIDE_ALLOWED")
        layer = path.relative_to(LIB).parts[0]
        if layer in LAYERS:
            for imp in IMPORT.findall(code):
                if not imp.startswith(LAYERS[layer]):
                    errors.append(f"{rel}: {layer} file imports {imp}")
            for m in NOT_A_DEFINITION.finditer(code):
                errors.append(f"{rel}:{line_of(code, m.start())}: `{m.group(0)}` "
                              f"({layer} is definitions only)")
        if rel == CLAIMS:
            for n, line in enumerate(code.split("\n"), 1):
                if line.strip() and not line[0].isspace() and not CLAIMS_COMMANDS.match(line):
                    errors.append(f"{rel}:{n}: only import, namespace, section, end, open, "
                                  f"variable and theorem are allowed at top level")
    for e in errors:
        print(e)
    n_spec = sum(1 for p in files if p.relative_to(LIB).parts[0] == "Spec")
    n_design = sum(1 for p in files if p.relative_to(LIB).parts[0] == "Design")
    print(f"{len(files)} files ({n_spec} Spec, {n_design} Design): "
          f"{'OK' if not errors else f'{len(errors)} problems'}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
