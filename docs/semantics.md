# Семантичні терми та їх обчислення

Матеріал відповідає Нікітченку, §1.3 (практикум, ПР 2). Програма перетворюється на терм програмної алгебри `A_SIPL` такими відображеннями:
- `sem_P: Prog → TFS`;
- `sem_S: Stm → TFS`;
- `sem_A: Aexp → TFA`;
- `sem_B: Bexp → TFB`.

Терм будується рекурсивно за AST ([src/semantics/term.ts](../src/semantics/term.ts)).

## Правила побудови

| Правило | Заміна |
|---------|--------|
| NS_Prog | `sem_P(begin S end) = sem_S(S)` |
| NS_Stm_As | `sem_S(x := a) = AS^x(sem_A(a))` |
| NS_Stm_Seq | `sem_S(S1; S2) = sem_S(S1) · sem_S(S2)` |
| NS_Stm_If | `sem_S(if b then S1 else S2) = IF(sem_B(b), sem_S(S1), sem_S(S2))` |
| NS_Stm_Wh | `sem_S(while b do S) = WH(sem_B(b), sem_S(S))` |
| NS_Stm_BE | `sem_S(begin S end) = (sem_S(S))` |
| NS_Stm_skip | `sem_S(skip) = id` |
| NS_A_Num, NS_A_Var | `sem_A(n) = n`, `sem_A(x) = x⇒` |
| NS_A_Add/Sub/Mult | `sem_A(a1 ∘ a2) = S^2(add/sub/mult, sem_A(a1), sem_A(a2))` |
| NS_B_eq/gr/less | `sem_B(a1 ∘ a2) = S^2(eq/gr/less, sem_A(a1), sem_A(a2))` |
| NS_B_or, NS_B_neg | `S^2(or, …)`, `S^1(neg, …)` |
| NS_A_If (SIPL-R) | `sem_A(if b then a1 else a2) = IF(sem_B(b), sem_A(a1), sem_A(a2))` |
| NS_A_Call (SIPL-R) | `sem_A(fn(a1, …, an)) = S^[x1,…,xn](fn, sem_A(a1), …, sem_A(an))` |
| NS_Func (SIPL-R) | `φ(fn) = sem_A(a)` для `func fn(x1, …, xn) = a` |

Правила NS_A_Par і NS_B_Par є тотожними. Дужки виразів зникають уже під час розбору, тому в покроковому виведенні ці кроки не показуються.

**Нотація друку.**
- Верхні індекси записано через `^`.
- Локальну суперпозицію Нікітченка `S^[x1,…,xn]` позначено так само; у практикумі вона записується як `S^{X,Y}`.
- `·` друкується лівоасоціативно. Дужки з правила NS_Stm_BE з'являються лише тоді, коли блок є операндом `·`.

Отже, для програми з ПР 1–2:

```text
AS^R(1) · WH(S^2(gr, Y⇒, 0), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1)))
```

Кожен вузол терма зберігає `ref = { nodeId, rule }`, тобто AST-вузол і правило, з яких його побудовано. `deriveTerm` повертає всю послідовність застосувань правил у вигляді «ліва частина = права частина»; її показує `sipl term --explain`.

## Обчислення (аплікація)

[src/semantics/evaluate.ts](../src/semantics/evaluate.ts) застосовує терм до стану за формулами табл. 1.5:

| Формула | Обчислення |
|---------|------------|
| AF_S | `S^n(f, g1, …, gn)(st) = f(g1(st), …, gn(st))` |
| AF_AS | `AS^x(fa)(st) = st ∇ [x ↦ fa(st)]` |
| AF_SEQ | `(fs1 · fs2)(st) = fs2(fs1(st))` |
| AF_IF | `IF(fb, fs1, fs2)(st) = fs1(st)`, якщо `fb(st) = true`, інакше `fs2(st)` |
| AF_WH | `WH(fb, fs)(st) = st_n`, де `st_(i+1) = fs(st_i)`, `fb(st_i) = true` для `i < n`, `fb(st_n) = false` |
| AF_DNM, AF_ID | `x⇒(st) = st(x)`, `id(st) = st` |
| AF_CALL (SIPL-R) | `S^[x1..xn](f, g1..gn)(st) = f(st ∇ [x1 ↦ g1(st), …])` |
| AF_BOT | `⊥(st)` не визначене |

Частковість враховано так, як у зауваженні 1.6: якщо будь-який аргумент формули невизначений, результат теж невизначений. Причини невизначеності:

| Причина | Коли виникає |
|---------|--------------|
| `unbound-variable` | змінна не має значення в стані |
| `overflow` | результат виходить за межі безпечних цілих |
| `bottom` | застосовано ⊥ (апроксимацію) |
| `iteration-limit` | цикл не завершився в межах бюджету |
| `call-depth` | рекурсія не завершилась у межах бюджету |

Інтерпретатора, окремого від термів, немає. `sipl run` застосовує до стану саме `sem_P(P)`. Тому виконання програми і є аплікацією її семантичного терму. `--trace` показує застосовані формули, наприклад:

```text
AF_WH WH(…): st0 = [X ↦ 5, Y ↦ 2, R ↦ 1], S^2(gr, Y⇒, 0)(st0) = true
AF_AS AS^R(…): [X ↦ 5, Y ↦ 2, R ↦ 1] ∇ [R ↦ 5] = [X ↦ 5, Y ↦ 2, R ↦ 5]
```
