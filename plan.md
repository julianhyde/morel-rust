# Datalog (hydromatic/morel#323) port plan

Port plan for morel-java commit `62581437ac9c8dc415b159fdc9d6abc7eb588e9a`,
which adds a Datalog frontend that compiles to Morel source.

## Strategy

Port the morel-java algorithm and structure as faithfully as possible: the
AST, the analyzer (safety + stratification), the translator (Datalog →
Morel source), and the orchestrator (parse → analyze → translate →
re-parse Morel → compile → eval → wrap as `Val::Variant`).

Each phase is a single commit (or small commit cluster) that leaves
`fullMake --no-clean` passing. Phases 1–3 are additive and isolated from
the evaluator, so they can be committed independently with low risk.
Phase 4 is the integration step.

## Parser technology

Use **lalrpop**, not pest, for the Datalog grammar. The Datalog grammar
is small (~12 productions, simple precedence), so it is a good test bed
for lalrpop in this codebase. If the experiment goes well we will later
migrate the main Morel parser from pest to lalrpop.

The morel-java parser is JavaCC (LL(k) recursive descent). Each JavaCC
production translates directly into a lalrpop rule.

## Scope of the morel-java commit

~2,200 LOC in `net.hydromatic.morel.datalog`:

| File | LOC | Purpose |
| --- | --: | --- |
| `DatalogParser.jj` | 378 | JavaCC grammar |
| `DatalogAst.java` | 402 | AST classes |
| `DatalogAnalyzer.java` | 333 | safety + stratification |
| `DatalogTranslator.java` | 619 | Datalog → Morel source |
| `DatalogEvaluator.java` | 307 | orchestrator |
| `DatalogException.java` |  35 | error type |

Plus:
- `BuiltIn.java`: +27 LOC (`DATALOG_EXECUTE/TRANSLATE/VALIDATE`)
- `Codes.java`:  +34 LOC (`Applicable` instances)
- `script/datalog.smli`: 749-line test script
- `data/map/adjacent-states.csv`: input file for `.input` directive

## Phases

### Phase 1 — Skeleton: AST + lalrpop parser

- New module `src/datalog/{mod.rs, ast.rs, parser.rs, error.rs}` plus a
  lalrpop grammar at `src/datalog/datalog.lalrpop`.
- AST mirrors `DatalogAst.java` 1:1 (`Program`, `Statement`,
  `Declaration`, `Param`, `Input`, `Output`, `Fact`, `Rule`, `BodyAtom`,
  `Comparison`, `Atom`, `Term`, `Variable`, `ArithmeticExpr`, `Constant`,
  `CompOp`, `ArithOp`).
- Parser entry point: `parse(input: &str) -> Result<Program, DatalogError>`.
- Add `lalrpop` to `[build-dependencies]` and `lalrpop-util` to
  `[dependencies]` in `Cargo.toml`. Wire `build.rs` to invoke lalrpop on
  any `.lalrpop` file under `src/`.
- Make the lint task aware of `.lalrpop` files (license header, line
  length, etc.) the same way it treats `.rs` and `.pest`.
- Unit tests round-trip a handful of programs (port the morel-java
  parser tests directly).
- Nothing wired into the language yet → `fullMake --no-clean` passes.

### Phase 2 — Analyzer + `Datalog.validate`

- Port `DatalogAnalyzer.java`:
  - Safety: every variable in the head appears positively in the body.
  - Stratification: no negation cycle in the relation dependency graph.
- Add `BuiltInFunction::DatalogValidate` of type `string -> string`.
  Returns either error text or schema/type info. Slot it into the strum
  metadata-driven library tables alongside the other built-ins.
- Add `tests/script/built-in/datalog.smli` exercising only `validate`
  (a couple of valid programs + a few error programs).
- `fullMake --no-clean` passes — only one new built-in.

### Phase 3 — Translator + `Datalog.translate`

- Port `DatalogTranslator.java`. This is the meatiest file: fixed-point
  fold over rules, seed/step decomposition, record-literal generation
  for tuples, projection of head variables.
- Add `BuiltInFunction::DatalogTranslate` of type
  `string -> string option`. Returns `SOME source` on success, `NONE` on
  failure (parse or analysis error).
- Extend `tests/script/built-in/datalog.smli` with `translate` cases
  whose expected output is the golden Morel source string.
- The translator does not yet re-parse its output, so there is no risk
  to the compiler or evaluator. `fullMake --no-clean` passes.

### Phase 4 — Evaluator + `Datalog.execute`

- Port `DatalogEvaluator.java` orchestration. Feed translator output
  into the existing `MorelParser` → `Compiles::prepare` → `eval`. Wrap
  the last binding as `Val::Variant` (the existing variant
  infrastructure already handles `LIST`, `BAG`, `RECORD`, etc.).
- Add `BuiltInFunction::DatalogExecute` of type `string -> variant`.
- Extend the test script with `execute` cases.
- `fullMake --no-clean` passes.

### Phase 5 — `.input` directive + full `datalog.smli` + docs

- Implement `loadInputFiles`: CSV reader that produces synthetic `Fact`s
  and injects them into the AST before analysis.
- Add `tests/data/map/adjacent-states.csv` (or wherever the existing
  `file.smli` test data lives — match that convention).
- Drop in the full 749-line `datalog.smli` script and register it in
  `tests/smile.rs`.
- Port `docs/datalog.md` and any `CLAUDE.md` additions.
- `fullMake --no-clean` passes.

## Notes

- `DatalogException` becomes a plain Rust `enum DatalogError` since we
  do not need exception-based control flow.
- Each built-in (validate / translate / execute) catches errors and
  surfaces them through the function's return type — execute returns a
  variant, translate returns `string option`, validate returns a
  diagnostic string.
- Phases 1–4 add code in isolation. Reverting any single phase leaves
  the prior phase intact.
- After phase 5, if the lalrpop experiment is successful, plan a
  follow-up to migrate the main Morel parser from pest to lalrpop.
