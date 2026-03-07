"""
verifier._legacy — Deprecated legacy verifier modules.

These modules contain the original Fitch-style proof checker that
predates the System E/H/T architecture.  They are preserved for
backward compatibility during the transition period (Phase 6.5).

New code should use:
  - verifier.unified_checker  (single entry point)
  - verifier.e_checker        (System E)
  - verifier.e_ast            (System E AST)
  - verifier.e_axioms         (System E axioms)
  - verifier.e_library        (theorem library)

Deprecated modules (re-exported here for import compatibility):
  - ast        → use e_ast
  - checker    → use unified_checker / e_checker
  - parser     → use e_parser (when available)
  - rules      → use e_axioms
  - library    → use e_library
  - matcher    → internal to legacy checker
  - scope      → internal to legacy checker
  - propositions → use e_library
"""
