# Архітектура

Ядро — бібліотека ([src/index.ts](../src/index.ts)). Командний рядок є лише її клієнтом, тому парсер, терми, обчислення й перевірки можна підключати до інших інструментів (редактор, веб-сторінка) без дублювання.

```text
 source ──► lexer ──► parser ──► AST ──► check
 (.sipl)    tokens,   recursive   typed nodes,   static diagnostics,
            //@       descent     id + span      input variables
            annotations              │
                                     ├──► semantics/term ──► Term (sem_P, φ) ──► print (course notation)
                                     │          │                └──► deriveTerm (rules NS_*)
                                     │          ▼
                                     │    semantics/evaluate  (formulas AF_*, partiality, budgets)
                                     │          │
                                     │          ├──► run: sem_P(P)(st)
                                     │          └──► fixpoint/approx: f0 = ⊥, f(k+1) = φ(fk)
                                     │                    └──► fixpoint/report ──► render (text, HTML)
                                     │
                                     └──► verify/wp ──► VCs ──► verify/verify
                                                               (bounded check + runs via evaluate)
```

## Шари і контракти

| Шар | Вхід → вихід | Контракт |
|-----|--------------|----------|
| [lexer.ts](../src/lexer.ts) | текст → `Token[]`, `Annotation[]` | `Token { kind, text, span }`; режими `program` / `assertion` |
| [parser.ts](../src/parser.ts) | токени → `Program` | помилки — `SiplError` з `Diagnostic` |
| [ast.ts](../src/ast.ts) | — | вузли з `id` (preorder) і `span`; `Expr` спільний для умов програми й тверджень |
| [check.ts](../src/check.ts) | текст → `CheckResult` | ніколи не кидає винятків на поганий вхід |
| [semantics/term.ts](../src/semantics/term.ts) | AST → `Term` | `ref = { nodeId, rule }` пов'язує терм з AST і правилом |
| [semantics/evaluate.ts](../src/semantics/evaluate.ts) | `Term` + `State` → стан, значення або `Undefined` | невизначеність є значенням, а не винятком |
| [fixpoint/approx.ts](../src/fixpoint/approx.ts) | програма + ім'я + k → `Term[]`, `ApproxTable` | `f0 … fk` поділяють підтерми |
| [fixpoint/report.ts](../src/fixpoint/report.ts) | таблиця + `--expect` → `ApproxReport` | дані для звітів |
| [verify/wp.ts](../src/verify/wp.ts) | анотована програма → `VC[]` | `hypothesis → goal` з `derivation` |
| [verify/verify.ts](../src/verify/verify.ts) | програма → `VerifyReport` | вердикт `refuted` / `unproven` / `inconclusive` / `checked-in-bounds` / `checked-in-sample` |

## Рішення

- **Інтерпретатор — це обчислення термів.** `sipl run` застосовує `sem_P(P)` до стану за формулами AF_*. Тому виконання збігається з композиційною семантикою курсу за побудовою, а апроксимації рекурсивних функцій використовують той самий механізм.
- **Розбір без зовнішніх бібліотек.** Рекурсивний спуск дає власні AST-вузли з точними позиціями та зрозумілими повідомленнями. Залежностей часу виконання немає.
- **Одна мова виразів для програм і анотацій.** Підстановка `Q[x ↦ a]` у `wp` працює безпосередньо з виразом програми. Лексер не пропускає в програми операції, що належать лише анотаціям.
- **Бюджети замість зависань.** Цикли, рекурсія і перевірка умов мають явні межі. Перевищення межі повідомляється як невизначеність з причиною.
