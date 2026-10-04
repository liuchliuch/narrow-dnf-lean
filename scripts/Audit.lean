import NarrowDNF
import Lean.Util.CollectAxioms

-- These closed checks prohibit unnoticed remaining Hatami/junta hypotheses.
example : NarrowDNF.HatamiArityLoad := NarrowDNF.hatami_arity_load
example : NarrowDNF.NarrowDNFApproximation := NarrowDNF.main_narrow_dnf
example : NarrowDNF.FriedgutAllBias := NarrowDNF.friedgut_all_bias

/- Audit by originating project module, not declaration namespace. This includes
private/generated declarations and any declaration placed in another namespace.
Each declaration's full transitive axiom closure is checked. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked := 0
  let mut origins : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some origin ← Lean.findModuleOf? name | continue
    if (`NarrowDNF).isPrefixOf origin then
      if !origins.contains origin then origins := origins.push origin
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
          throwError "Disallowed transitive axiom {ax} in {name}, originating in {origin}"
      checked := checked + 1
  logInfo m!"AUDITED PROJECT MODULES: {origins}"
  logInfo m!"PASS: origin-complete audit of {checked} project declarations in {origins.size} modules; only propext, Classical.choice, Quot.sound."
