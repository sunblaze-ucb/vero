import Pythonconstraint.Impl.Csp

/-!
# Pythonconstraint.Bundle

Per-package implementation bundle for the `Pythonconstraint` root package.
Collects all API signatures into one structure.

DO NOT MODIFY — benchmark infrastructure.
-/

structure PythonconstraintBundle where
  holds         : Pythonconstraint.HoldsSig
  getSolutions  : Pythonconstraint.GetSolutionsSig
  getSolution   : Pythonconstraint.GetSolutionSig
  solutionCount : Pythonconstraint.SolutionCountSig
