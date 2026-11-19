# Changelog

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/); versions follow [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Fixed
- `verify` no longer passes when part of the check tested nothing (vacuous conditions, no run from a state satisfying the precondition): the new verdict `inconclusive` exits with code 2. `--max-cases 0` is rejected.
- Integer overflow in a run or an annotation makes the run inconclusive instead of refuting a correct program.
- Ghost variables that occur only in the postcondition, invariants or variants now range over the box in runs.
- Nested parenthesised conditions are parsed in linear time instead of exponential time.
- Programs too long or nested too deeply for the call stack get diagnostic E102 or a clear CLI message instead of an internal error.

### Changed
- Node.js 22 or newer is required; CI runs lint, tests and the package build as separate stages.

## [0.1.0] - 2026-11-19

### Added
- Formal grammars (W3C EBNF) for SIPL, its recursive extension SIPL-R and the annotation language.
- Lexer and recursive-descent parser producing a typed AST with source spans; static checks for functions, arity and uninitialised variables.
- Semantic terms of programs and functionals φ of recursive functions in the course notation, with the derivation by rules NS_*.
- Term evaluator following the formulas AF_* with partiality, used as the runtime of SIPL and SIPL-R.
- Least-fixpoint approximations f0 = ⊥, f(k+1) = φ(fk), their application to states, tabulation over test grids, monotonicity and expected-function checks, text and HTML reports.
- Correctness assistant for loop programs: verification conditions by weakest preconditions, bounded checking with counterexamples, execution runs, partial and total correctness.
- `sipl` command-line interface with JSON output and stable exit codes.
- Continuous integration workflow.
