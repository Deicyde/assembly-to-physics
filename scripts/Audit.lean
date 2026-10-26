import AsmPhys

/-!
# Claims audit

Run with `lake env lean scripts/Audit.lean` after `lake build`. It fails (exit code 1) unless:

1. every declaration of the module `AsmPhys.Claims` is a theorem, apart from the auxiliary
   definitions Lean generates for its statements;
2. every constant of this library that a claim's statement depends on is defined in `AsmPhys.Spec`
   or `AsmPhys.Design`. The dependencies are followed through the types and bodies of definitions
   and the constructors of inductive types. Theorems are leaves: by proof irrelevance no proof
   term inside a statement affects its meaning. Mathlib and the Lean core are not traversed;
3. every module of `AsmPhys.Spec` imports only Mathlib, the Lean core and `AsmPhys.Spec`, and every
   module of `AsmPhys.Design` only these and `AsmPhys.Design` (read from the compiled modules, so
   every form of `import` counts);
4. every claim, and every declaration of `AsmPhys.Spec` and `AsmPhys.Design`, depends only on the
   axioms `propext`, `Classical.choice` and `Quot.sound`.

It also lists the definitions of `AsmPhys.Spec` and `AsmPhys.Design` that no claim reaches. With
the environment variable `AUDIT_DEPS=1` it prints, for each claim, the Spec and Design definitions
its statement depends on: the reading list for that claim.
-/

open Lean Elab Command

namespace AsmPhysAudit

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def moduleOf (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

def inLib (mod : Name) : Bool := (`AsmPhys).isPrefixOf mod

def specLayer (mod : Name) : Bool := (`AsmPhys.Spec).isPrefixOf mod

def designLayer (mod : Name) : Bool := (`AsmPhys.Design).isPrefixOf mod

def trustedLayer (mod : Name) : Bool := specLayer mod || designLayer mod

/-- Mathlib, its dependencies and the Lean core. -/
def upstream (mod : Name) : Bool :=
  [`Mathlib, `Init, `Std, `Lean, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
    `LeanSearchClient, `ImportGraph].any (·.isPrefixOf mod)

/-- Declarations Lean generates: `deriving` instances and the helpers of inductive types. -/
def generated (c : Name) : Bool :=
  c.components.any (fun s => s.toString.startsWith "inst") ||
    match c with
    | .str _ s => ["ctorIdx", "noConfusionType", "ctorElimType", "ofNat", "below"].contains s
    | _ => false

/-- The constants a declaration depends on: its type, plus the body of a definition or the
constructors of an inductive type. A theorem's proof is not followed. -/
def mentions (ci : ConstantInfo) : Array Name :=
  let body := match ci with
    | .defnInfo d => d.value.getUsedConstants
    | .inductInfo i => i.ctors.toArray
    | _ => #[]
  ci.type.getUsedConstants ++ body

/-- The library constants a statement depends on, from the constants it mentions: the constants
visited, and the library constants reached outside the trusted layer. -/
partial def reach (env : Environment) (roots : Array Name) : NameSet × Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut stack := roots
  let mut bad := #[]
  while h : stack.size > 0 do
    let c := stack.back
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some mod := moduleOf env c | continue
    if !inLib mod then continue
    let some ci := env.find? c | continue
    if ci matches .thmInfo _ then continue
    if trustedLayer mod || (mod == `AsmPhys.Claims && c.isInternalDetail) then
      stack := stack ++ mentions ci
    else
      bad := bad.push c
  return (seen, bad)

/-- A definition or inductive type a reader would look up (not a projection, constructor,
recursor or generated helper). -/
def userFacing (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _) | some (.inductInfo _) =>
    !c.isInternalDetail && !isAuxRecursor env c && !isNoConfusion env c &&
      !env.isProjectionFn c && !generated c
  | _ => false

end AsmPhysAudit

open AsmPhysAudit in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut failures : Array String := #[]
  let claims := env.constants.toList.filter fun (c, _) =>
    moduleOf env c == some `AsmPhys.Claims && !c.isInternalDetail
  -- 1. claims are theorems
  for (c, ci) in claims do
    unless ci matches .thmInfo _ do
      failures := failures.push s!"{c} in AsmPhys.Claims is not a theorem"
  let claimThms := (claims.filter fun (_, ci) => ci matches .thmInfo _).toArray.qsort
    (fun a b => a.1.toString < b.1.toString)
  -- 2. statements depend only on the trusted layer
  let mut reached : NameSet := {}
  let mut deps : Array (Name × Array Name) := #[]
  for (c, ci) in claimThms do
    let (seen, bad) := reach env ci.type.getUsedConstants
    reached := seen.foldl (·.insert ·) reached
    for b in bad do
      failures := failures.push
        s!"the statement of {c} depends on {b}, defined in {(moduleOf env b).getD .anonymous}"
    let mine := seen.toArray.filter fun d =>
      (moduleOf env d).any trustedLayer && userFacing env d
    deps := deps.push (c, mine.qsort (·.toString < ·.toString))
  -- 3. imports of the trusted layer
  for h : i in [0:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]
    let some data := env.header.moduleData[i]? | continue
    for imp in data.imports do
      let ok :=
        if specLayer mod then upstream imp.module || specLayer imp.module
        else if designLayer mod then upstream imp.module || trustedLayer imp.module
        else true
      unless ok do
        failures := failures.push s!"{mod} imports {imp.module}"
  -- 4. axioms
  let trusted := env.constants.toList.filter fun (c, _) => (moduleOf env c).any trustedLayer
  for c in claimThms.map (·.1) ++ (trusted.map (·.1)).toArray do
    for a in ← collectAxioms c do
      unless standardAxioms.contains a do
        failures := failures.push s!"{c} depends on the axiom {a}"
  -- report
  let unreached := trusted.filter fun (c, _) => !reached.contains c && userFacing env c
  logInfo m!"{claimThms.size} claims, {trusted.length} declarations in AsmPhys.Spec and \
    AsmPhys.Design, {failures.size} failures"
  unless unreached.isEmpty do
    logInfo m!"Spec/Design definitions no claim reaches: {unreached.map (·.1)}"
  if (← IO.getEnv "AUDIT_DEPS").isSome then
    for (c, ds) in deps do
      logInfo m!"{c} depends on {ds.size} Spec/Design definitions: {ds.toList}"
  unless failures.isEmpty do
    throwError "audit failed:\n{String.intercalate "\n" failures.toList}"
