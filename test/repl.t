Batch input uses the same REPL without prompts; EOF exits cleanly.

  $ printf '%s\n' ':show' ':strategy' '(λx.x) y' ':load (λx.x) ((λy.y) z)' ':step' ':run' ':reset' ':quit' | lambada
  No term loaded.
  nor
  y
  [nor; 1 step(s); normal form for strategy]
  (λx.x) ((λy.y) z)
  (λy.y) z
  [nor; 1 step(s); step limit reached]
  z
  [nor; 1 step(s); normal form for strategy]
  (λx.x) ((λy.y) z)

Strategy differences and bounded divergence (even when a step leaves Ω unchanged).

  $ printf '%s\n' ':steps 2' ':strategy cbv' '(λx.z) ((λx.x x) (λx.x x))' ':strategy cbn' ':run' ':strategy ao' 'λx.(λy.y) x' ':strategy nor' '(λx.λy.y) z' | lambada
  Step limit: 2
  Strategy: cbv
  (λx.z) ((λx.x x) (λx.x x))
  [cbv; 2 step(s); step limit reached]
  Strategy: cbn
  z
  [cbn; 1 step(s); normal form for strategy]
  Strategy: ao
  λx.x
  [ao; 1 step(s); normal form for strategy]
  Strategy: nor
  λy.y
  [nor; 1 step(s); normal form for strategy]

Invalid input does not destroy the current expression or settings.

  $ printf '%s\n' ':load x' 'x)' ':show' ':strategy invalid' ':strategy' ':steps 0' ':steps nope' ':steps 100001' ':steps' ':wat' ':quit extra' ':show' | lambada
  x
  Parse error: check the complete expression and parentheses.
  x
  Unknown strategy: use cbn, cbv, nor, or ao.
  nor
  Step limit must be an integer from 1 to 100000.
  Step limit must be an integer from 1 to 100000.
  Step limit must be an integer from 1 to 100000.
  Step limit: 1000
  Unknown command or invalid arguments. Type :help.
  Unknown command or invalid arguments. Type :help.
  x

Alpha-renamed results can be pasted back into the REPL.

  $ printf '%s\n' '(λx.λy.x y) y' "λy'.y y'" ':load (λx.x) z' ':strategy cbn' ':step' ':step' ':quit' 'ignored' | lambada
  λy'.y y'
  [nor; 1 step(s); normal form for strategy]
  λy'.y y'
  [nor; 0 step(s); normal form for strategy]
  (λx.x) z
  Strategy: cbn
  z
  [cbn; 1 step(s); normal form for strategy]
  z
  [cbn; 0 step(s); normal form for strategy]

  $ printf '' | lambada
