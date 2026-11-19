# SIPL Correctness & Fixpoint Toolkit

[![CI](https://github.com/luckymelon257/sipl-toolkit/actions/workflows/ci.yml/badge.svg)](https://github.com/luckymelon257/sipl-toolkit/actions/workflows/ci.yml)

Курсовий проєкт з дисципліни «Теорія програмування»: набір інструментів на Node.js/TypeScript для мови **SIPL** та її рекурсивного розширення **SIPL-R**. Інструменти:
- будують семантичні терми програм;
- будують апроксимації найменшої нерухомої точки рекурсивних функцій і тестують їх;
- перевіряють коректність циклічних програм за інваріантами з контрприкладами.

## Обрані завдання

| ID | Завдання | Бали | Де реалізовано |
|----|----------|-----:|----------------|
| CORE-02 | Парсер і типізоване AST з `SourceSpan` | 1.5 | [src/lexer.ts](src/lexer.ts), [src/parser.ts](src/parser.ts), [src/ast.ts](src/ast.ts), [src/check.ts](src/check.ts) |
| SEM-01 | Автоматична побудова семантичного терму в нотації курсу | 2.0 | [src/semantics/term.ts](src/semantics/term.ts), [src/semantics/print.ts](src/semantics/print.ts) |
| REC-01 | Рекурсивні функції: синтаксис, AST, парсер, runtime | 2.0 | [grammar/sipl-r.ebnf](grammar/sipl-r.ebnf), [src/semantics/evaluate.ts](src/semantics/evaluate.ts) |
| REC-02 | Функціонал φ і ланцюг апроксимацій f0 = ⊥, f1 = φ(f0), … | 2.5 | [src/fixpoint/approx.ts](src/fixpoint/approx.ts) |
| REC-03 | Автоматизоване тестування апроксимацій і візуалізація збіжності | 1.5 | [src/fixpoint/report.ts](src/fixpoint/report.ts), [src/fixpoint/render.ts](src/fixpoint/render.ts) |
| SEM-04 | Асистент доведення коректності циклічних програм | 2.5 | [src/verify/wp.ts](src/verify/wp.ts), [src/verify/verify.ts](src/verify/verify.ts) |
| REL-01 | CI: lint, type-check, тести, збірка пакета | 0.5 | [.github/workflows/ci.yml](.github/workflows/ci.yml) |
| | **Разом заявлено** | **12.5** | підсумкова оцінка обмежена 10 балами |

## Встановлення

Потрібен Node.js 20 або новіший.

```bash
git clone https://github.com/luckymelon257/sipl-toolkit.git
cd sipl-toolkit
npm ci
npm run build
npm link          # робить команду `sipl` доступною глобально (необов'язково)
```

Без `npm link` команду можна викликати як `node dist/cli.js …`.

## Швидкий старт

```bash
sipl check examples/gcd.sipl                       # синтаксис і статичні перевірки
sipl run examples/power.sipl -s X=5 -s Y=2         # result: [X ↦ 5, Y ↦ 0, R ↦ 25]
sipl run examples/power.sipl -s X=5,Y=2 --trace    # застосовані формули AF_*
sipl term examples/power.sipl                      # семантичний терм
sipl term examples/power.sipl --explain            # покрокова побудова за правилами NS_*
sipl approx examples/rec-div.sipl -k 2 -s X=7,Y=4 --explain
sipl approx examples/rec-div.sipl -k 6 --grid X=0..20,Y=1..6 --expect "X div Y" --html report.html
sipl verify examples/verify/gcd.sipl               # VC, контрприклади, прогони
```

Кожна команда має режим `--json` для інтеграцій. Формат JSON і коди завершення описані в [docs/cli.md](docs/cli.md).

### Семантичний терм (SEM-01)

```text
$ sipl term examples/power.sipl
sem_P = AS^R(1) · WH(S^2(gr, Y⇒, 0), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1)))
```

Терм збігається з прикладом практикуму (ПР 2). З `--explain` видно кожне застосування правила, наприклад `[NS_Stm_Seq] sem_S(R := 1; while …) = sem_S(R := 1) · sem_S(while …)`.

### Рекурсивна функція та апроксимації (REC-01…03)

```text
$ cat examples/rec-div.sipl
program
  func f(X, Y) = if X < Y then 0 else f(X - Y, Y) + 1
begin
  Q := f(A, B)
end

$ sipl approx examples/rec-div.sipl -k 2 -s X=7,Y=4
f0 = ⊥
f1 = IF(S^2(less, X⇒, Y⇒), 0, ⊥)
f2 = IF(S^2(less, X⇒, Y⇒), 0, S^2(add, S^[X,Y](IF(S^2(less, X⇒, Y⇒), 0, ⊥), S^2(sub, X⇒, Y⇒), Y⇒), 1))

f0([X ↦ 7, Y ↦ 4]) = ⊥ (⊥ is undefined on [X ↦ 7, Y ↦ 4])
f1([X ↦ 7, Y ↦ 4]) = ⊥ (⊥ is undefined on [X ↦ 7, Y ↦ 4])
f2([X ↦ 7, Y ↦ 4]) = 1
```

З `--grid` інструмент будує таблицю значень f0…fk на тестових станах. У стовпці `first` видно, на якій апроксимації вхід стає визначеним. Інструмент перевіряє монотонність ланцюга і порівнює значення з очікуваною функцією `--expect`. З `--html` створюється звіт із тепловою картою області визначеності та графіком збіжності.

### Асистент коректності (SEM-04)

Анотації записуються коментарями `//@` і не змінюють мову SIPL:

```text
//@ pre: M = m ∧ N = n ∧ m > 0 ∧ n > 0
begin
  //@ invariant: M > 0 ∧ N > 0 ∧ gcd(M, N) = gcd(m, n)
  //@ variant: M + N
  while ¬M = N do
    if M > N then M := M - N else N := N - M
end
//@ post: M = gcd(m, n) ∧ N = gcd(m, n)
```

`sipl verify` генерує умови коректності:
- вхід (база індукції);
- збереження інваріанта (крок індукції);
- вихід із циклу;
- обмеженість і спадання варіанта (завершуваність).

Інструмент показує, як кожну умову отримано через wp. Кожну умову він перевіряє на всіх станах обмеженого куба й дає контрприклад, якщо вона хибна. Потім запускає програму з кожного стану, що задовольняє передумову. Так асистент відрізняє справжню помилку від слабкого (неіндуктивного) інваріанта. Подробиці в [docs/verification.md](docs/verification.md).

## Структура

```text
grammar/            формальні граматики: sipl.ebnf, sipl-r.ebnf, assertions.ebnf
src/
  lexer.ts          лексика, позиції, анотації //@
  parser.ts         рекурсивний спуск → типізоване AST
  ast.ts            вузли AST з id та SourceSpan
  check.ts          статичні перевірки (функції, арність, вхідні змінні)
  semantics/        терми (sem_P, sem_S, sem_A, sem_B, φ), друк, обчислення (AF_*)
  fixpoint/         апроксимації ННТ, тестування, текстовий і HTML-звіт
  verify/           wp, умови коректності, перевірка на кубі станів, прогони
  assertion.ts      мова тверджень анотацій
  cli.ts            командний рядок
examples/           приклади SIPL/SIPL-R, некоректні програми, анотовані програми
tests/              автоматичні тести (node:test), golden-файли термів
docs/               документація
```

Як дані проходять між шарами: [docs/architecture.md](docs/architecture.md).

## Розробка

```bash
npm run lint        # ESLint
npm run typecheck   # tsc без генерації файлів
npm test            # 120+ тестів, поріг покриття рядків 80% (c8)
npm run build       # збірка в dist/
```

Golden-файли семантичних термів лежать у `tests/golden/`. Після свідомої зміни нотації їх оновлюють так: `UPDATE_GOLDEN=1 npm test`.

## Обмеження

- **Перевірка в межах куба — це не доведення.** Асистент коректності перевіряє умови на всіх станах із заданого діапазону (за замовчуванням [-3, 8]). Якщо станів забагато, він перевіряє вибірку і тоді повідомляє `checked-in-sample`. Результат `checked-in-bounds` є свідченням коректності. Асистент знаходить контрприклади, але не доводить загальне твердження.
- **Цілі числа обмежені** безпечним діапазоном JavaScript (±2⁵³−1). За його межами значення вважається невизначеним (`overflow`), а не неправильним.
- **Незавершуваність не розпізнається, а обрізається.** Цикли й рекурсія обмежені бюджетами: ітерацій (100 000) і глибини викликів (500); номер апроксимації `k` не більший за 200. Результат «undefined: iteration-limit» означає «не завершилось у межах бюджету».
- **`div` і `mod` не входять у мову програм**, бо їх немає в БНФ курсу. Їх можна використовувати лише в анотаціях і в `--expect`.
- **Асистент коректності не підтримує виклики функцій.** Для рекурсивних функцій призначена команда `sipl approx`.

## Джерела

1. Нікітченко М.С. Теорія програмування. — К.: КНУ ім. Тараса Шевченка, 2020. Використано §1.1–1.4 (синтаксис, семантика, коректність SIPL) і §5.7 (рекурсія, ННТ, SIPL-R).
2. Шишацька О.В., Криволап А.В., Шишацький А.В. Теорія програмування. Практикум. — 2024. Використано ПР 1–3 і ПР 7.

## Ліцензія

[MIT](LICENSE)
