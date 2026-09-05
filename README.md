# [Lambada](https://youtu.be/iyLdoQGBchQ?si=j_-c54sP1RnX9sA3)

A lambda calculus interpreter with small-step operational semantics.

## Build and test in Docker

```sh
docker build -f Dockerfile.test -t lambada-test .
docker run --rm lambada-test
```

No host OCaml/opam installation is needed. The suite includes the original
expect tests, substitution/parser regressions, scripted REPL sessions, and
10,000 deterministic generated terms checked against an independent de Bruijn
evaluator. Both printers are checked for parse/print round-trip correctness.

## REPL

```sh
docker run --rm -it lambada-test opam exec -- dune exec lambada
```

Enter a term to evaluate it using normal order by default:

```text
lambada> (λx.x) y
y
[nor; 1 step(s); normal form for strategy]
lambada> :load (λx.x) ((λy.y) z)
(λx.x) ((λy.y) z)
lambada> :step
(λy.y) z
[nor; 1 step(s); step limit reached]
lambada> :run
z
[nor; 1 step(s); normal form for strategy]
```

| Command | Action |
| --- | --- |
| `:strategy cbn\|cbv\|nor\|ao` | Choose a strategy; omit the argument to show it |
| `:steps N` | Set the per-run reduction limit (1–100000; default 1000) |
| `:load TERM` | Load a term without reducing it |
| `:step` | Perform one beta-reduction |
| `:run` | Continue evaluating up to the step limit |
| `:show` | Print the current term |
| `:reset` | Restore the last successfully loaded input |
| `:help` | Show commands |
| `:quit` | Exit; EOF also works |

After reaching the step limit, use `:run` to continue or change strategies.
The limit bounds beta-reductions, not memory use or the cost of an individual
reduction. Piped input works without banners or prompts (use Docker's `-i`
without `-t`). Parse errors leave the current term intact.

## Syntax and strategies

The parser accepts `λ` or `\`, left-associative applications, nested abstractions,
and apostrophe-suffixed variable names produced by alpha-renaming. Leading/trailing
whitespace is allowed; malformed or trailing input is rejected. Lambda bodies
extend as far right as possible: `λx.x y` means `λx.(x y)`.

REPL output uses only necessary parentheses via `Ast.pretty_term`.
`Ast.string_of_term` retains fully parenthesized output for existing callers.

CBN and CBV are weak strategies (they do not reduce under lambdas); NOR and AO
reduce under lambdas. CBV evaluates arguments before substitution; AO additionally
normalizes the function body first. Open irreducible terms count as CBV values.
CBN and NOR can discard unused divergent arguments; CBV and AO cannot.

See `lib/interpreter/interpreter.ml` and `test/` for examples.

## TODO

- [x] REPL
- [x] Reduce the number of parentheses in the output
- [x] Translate Russian comments into English
- [x] Dance
