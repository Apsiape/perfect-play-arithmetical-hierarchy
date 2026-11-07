import Sigma2.Main
import Sigma2.MainPaper
import Sigma2.SharedFamily
import Lean.Util.CollectAxioms

/-! Final-root audit: declaration types and opaque bodies, not import membership. -/
set_option maxHeartbeats 20000000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let modules : Array Name := #[`Sigma2.CompilerHonestStructuralAssembly, `Sigma2.CompilerHonestBase, `Sigma2.CompilerHonestGraph, `Sigma2.CompilerHonestListRows, `Sigma2.CompilerRegisterIdentities, `Sigma2.CompilerHonestRowAlgebra, `Sigma2.CompilerHonestRowBlocks, `Sigma2.CompilerHonestRows, `Sigma2.CompilerHonestStructural, `Sigma2.CompilerHonestTransport, `Sigma2.CompilerApproxIndex, `Sigma2.CompilerApproxEnergy, `Sigma2.CompilerApproxBound, `Sigma2.CompilerApproxEvents, `Sigma2.CompilerApproxStrategy, `Sigma2.CompilerApproxBase, `Sigma2.CompilerCompleteSupport, `Sigma2.CompilerCompleteness, `Sigma2.CompilerObligations, `Sigma2.MainPaper, `Sigma2.Main, `Sigma2.UpperGridCertificate, `Sigma2.UpperBoxStages]
  let roots : List Name := [`Sigma2.CompilerObligations.obligations_all,
    `Sigma2.theoremA, `Sigma2.theoremA_paper, `Sigma2.theoremA_shared_family]
  let explicitForbidden : List Name := [`Sigma2.Compiler.lemma_4_4_strong,
    `Sigma2.Compiler.lemma_4_4_four_bridge_compiler,
    `Sigma2.Compiler.compileCode, `Sigma2.Compiler.compileCode_computable,
    `Sigma2.Compiler.compileCode_correct, `Sigma2.Compiler.approximate_compilation,
    `Sigma2.Reduction.gameCode]
  let mut forbidden := explicitForbidden
  let mut newRoots : List Name := []
  for (n, ci) in env.constants.toList do
    if n.toString.startsWith "Sigma2.Compiler." then
      let ax := (← Lean.collectAxioms n).toList
      if ax.contains `sorryAx then
        unless forbidden.contains n do forbidden := n :: forbidden
    if let some idx := env.getModuleIdxFor? n then
      if modules.contains env.allImportedModuleNames[idx]! then
        if ci matches .axiomInfo _ then throwError "New axiom declaration {n}"
        let ax := (← Lean.collectAxioms n).toList
        for a in ax do
          unless standard.contains a do throwError "Unexpected axiom {a} in {n}"
        logInfo m!"DECL30:{toJson (n.toString, ax.map Name.toString) |>.compress}"
        newRoots := n :: newRoots
  let mut todo := roots ++ newRoots
  let mut seen : NameSet := {}
  let mut graph : Std.HashMap Name (Array Name) := {}
  let mut admitted : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing reachable declaration {n}"
    let deps := ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants |>.getD #[])
    graph := graph.insert n deps
    if deps.contains `sorryAx then admitted := admitted.insert n
    todo := deps.toList ++ todo
  for root in roots ++ newRoots do
    todo := [root]
    let mut closure : NameSet := {}
    while !todo.isEmpty do
      let n := todo.head!
      todo := todo.tail!
      if closure.contains n then continue
      closure := closure.insert n
      todo := ((graph[n]?).getD #[]).toList ++ todo
    let ledger := closure.toList.filter admitted.contains
    unless ledger.isEmpty do throwError "Nonempty admission ledger {root}: {ledger}"
    if closure.contains `sorryAx then throwError "sorryAx reachable from {root}"
    for n in forbidden do
      if closure.contains n then throwError "Legacy compiler dependency {root} -> {n}"
    if roots.contains root then
      let ax := (← Lean.collectAxioms root).toList
      unless ax.length == 3 && standard.all ax.contains do
        throwError "Root must use exactly the standard axioms: {root}: {ax}"
      elabCommand (← `(#print axioms $(mkIdent root)))
      logInfo m!"ROOT30:{toJson (root.toString, ledger.map Name.toString, closure.size, ax.map Name.toString) |>.compress}"
      logInfo m!"CLOSURE30:{toJson (root.toString, closure.toList.map Name.toString) |>.compress}"
  for (root, stmt) in [(`Sigma2.theoremA, ``Sigma2.TheoremAStatement),
      (`Sigma2.theoremA_paper, ``Sigma2.TheoremAStatement),
      (`Sigma2.theoremA_shared_family, ``Sigma2.SharedFamilyHardness)] do
    let some ci := env.find? root | throwError "Missing final theorem {root}"
    unless ci matches .thmInfo _ do throwError "Final root is not a theorem {root}"
    unless ci.levelParams.isEmpty do throwError "Unexpected theorem universe parameters {root}"
    unless ci.type == mkConst stmt do
      throwError "Final theorem takes arguments or has an unexpected type: {root} : {ci.type}"
    if env.contains `Sigma2.UpperRealArithmetic.TarskiDecision then
      throwError "TarskiDecision is still declared"
    logInfo m!"HYPOTHESIS30:{root} : {stmt} (no arguments, no hypotheses)"
  logInfo m!"FORBIDDEN30:{toJson (forbidden.map Name.toString) |>.compress}"
  logInfo m!"DECLCOUNT30:{newRoots.length}"
  logInfo m!"TRAVERSED30:{seen.size}"

#print Sigma2.CompilerObligations.obligations_all
#print Sigma2.theoremA
#print Sigma2.theoremA_paper
#print Sigma2.theoremA_shared_family
#print axioms Sigma2.theoremA
#print axioms Sigma2.theoremA_paper
#print axioms Sigma2.theoremA_shared_family
