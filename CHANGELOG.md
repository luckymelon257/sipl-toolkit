# Changelog

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/); versions follow [Semantic Versioning](https://semver.org/).

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
