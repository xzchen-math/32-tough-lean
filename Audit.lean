import Broersma
import Lean.Util.CollectAxioms

/-! Machine-checked axiom audit. This checks proved declarations, not the
existence of a proof of `MainTheoremStatement`. The unconditional main
theorem is separately required by `python3 verify.py --require-complete`. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [
    ``propext, ``Classical.choice, ``Quot.sound,
    ``Broersma.External.split_hamiltonian,
    ``Broersma.External.two_factor,
    ``Broersma.External.coabsorbable_successors,
    ``Broersma.External.chvatal_properties]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Broersma).isPrefixOf name then
      declarations := declarations + 1
      if info matches .thmInfo _ then
        theorems := theorems + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} in {name}"
  logInfo m!"AXIOM AUDIT PASSED: {declarations} Broersma declarations, {theorems} theorems; no sorryAx or unapproved axiom."
  logInfo "MAIN THEOREM STATUS: OPEN. main_of_configuration requires the unproved InternalConstruction premise."

#print axioms Broersma.TwoK2Free.neighbors_comparable
#print axioms Broersma.TwoK2Free.edge_components_equal
#print axioms Broersma.longest_admissible_path_dominating
#print axioms Broersma.ExtremalPair.exchange
#print axioms Broersma.FinalConfiguration.impossible
#print axioms Broersma.main_of_configuration
#print axioms Broersma.split_completion_hamiltonian
#print axioms Broersma.near_cycle_external_structure
#print axioms Broersma.sharpness

#check Broersma.MainTheoremStatement
#check Broersma.main_of_configuration
