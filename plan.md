<!--
{% comment %}
Licensed to Julian Hyde under one or more contributor license
agreements.  See the NOTICE file distributed with this work
for additional information regarding copyright ownership.
Julian Hyde licenses this file to you under the Apache
License, Version 2.0 (the "License"); you may not use this
file except in compliance with the License.  You may obtain a
copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing,
software distributed under the License is distributed on an
"AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
either express or implied.  See the License for the specific
language governing permissions and limitations under the
License.
{% endcomment %}
-->
# Command-line editing with Rustyline — analysis and implementation plan

Analysis and plan for issue #45: add line editing (Emacs/vi keybindings,
up-arrow history, history persistence) to the interactive shell using the
[rustyline](https://crates.io/crates/rustyline) crate. Covers the
architectural question raised alongside it: should the code be reorganized
so there is a clean separation between the *shell* (terminal front end) and
the Morel *process* (a component that takes a stream of requests and
produces responses)?

## 1. Current state: `Shell` conflates three roles

`src/shell/main.rs` (~1700 lines) contains one struct, `Shell`, doing three
jobs:

1. **Engine** — `process_statement(&mut self, code, expected) ->
   ShellResult<String>`, plus `Environment`, `Session`, `LinkTable`,
   property handling (`Sys.set`), and `use`-file execution. This is
   already a request/response interface.
2. **Statement assembly** — buffering lines until the buffer ends with `;`
   at comment depth 0. Duplicated in *three places*: the `run` loop, in
   `execute_use_file`, and in the `.smli` expected-output lookahead
   handling. A rustyline `Validator` would be the fourth copy.
3. **Front end** — prompting (`- `/`= `), echo, banner, the idempotent
   `>`-lookahead and `output_matcher` comparison, reading from a generic
   `R: Read`, writing to a generic `W: Write`.

The engine boundary already exists de facto; three consumers funnel
through `process_statement`:

* `wasm.rs` — `MorelShell::process_statement(&mut self, input)`
  (request in, response out, verbatim);
* `run_command` — the `-e`/`--eval` path;
* the `run` loop — pipes, scripts, and today's line-at-a-time
  "interactive" mode.

## 2. Is the shell/process separation needed? Yes — and it is cheap

We do not need to *build* a request/response process; we need to *name*
the one we have. Morel-Java already made this exact split, which gives a
propagation-friendly vocabulary:

| morel-java | role | proposed morel-rust |
|---|---|---|
| `Kernel` (`execute(code) -> List<String>`) | the "process": statement in, output lines out | `Kernel` (extracted from today's `Shell`) |
| `Main` | line loop over Reader/Writer (scripts, pipes) | `ScriptRunner` (today's `Shell::run`) |
| `Shell` | jline3 terminal front end | `Shell` (new, rustyline) |

Anything grander — channels, an actor loop, async — is not recommended.
`execute(&mut self, &str) -> Result<String>` is the whole protocol. A
stream abstraction on top of it is unearned generality until there is a
second concurrent client (an LSP server or a Jupyter kernel — at which
point `Kernel` is exactly the thing such a client would wrap).

## 3. Naming

"Shell" is currently confusing on three axes: module `shell/`, struct
`Shell`, and file `shell/main.rs` vs. the binary's `src/main.rs` — and
Morel-Rust's `Shell` means roughly the opposite of Morel-Java's `Shell`.
Proposed names:

* **`Kernel`** — the engine. Preferred over `Engine`/`Interpreter`
  because it matches Morel-Java's `Kernel` exactly, and it is the
  established Jupyter term for "the process that executes code and
  returns outputs". (`Session` and `Evaluator` are taken by `eval::`.)
* **`Shell`** — *reclaimed* for the new rustyline front end, aligning
  with Morel-Java, where `Shell` is the jline terminal UI. A shell is
  the interactive skin around a kernel; after this change that is true
  in both repositories.
* **`ScriptRunner`** (or `LineRunner`) — the existing
  `R: Read`/`W: Write` loop: pipes, `.smli` scripts, `use` files.
* **`StatementSplitter`** (module `shell/statement.rs`) —
  `comment_depth` plus `fn is_complete(&str) -> bool`; the single
  implementation shared by the runner, `use`-file execution, and the
  rustyline `Validator`.

File layout: dissolve `shell/main.rs` into
`shell/{kernel.rs, runner.rs, statement.rs, terminal.rs}`. Keep the
module named `shell` — renaming the module churns every import for
little gain; the struct names carry the disambiguation.
(`shell/terminal.rs` could instead be `shell/interactive.rs` if
`Shell`-inside-`terminal.rs` reads oddly.)

## 4. What is genuinely shared with the script runner

| concern | interactive (rustyline) | piped stdin | scripts / `use` | lives in |
|---|---|---|---|---|
| execution, env persistence, props, `use` | yes | yes | yes | `Kernel` |
| statement completeness (`;` + comment depth) | yes (Validator) | yes | yes | `StatementSplitter` |
| error formatting (`MorelError` to text) | yes | yes | yes | `Kernel` |
| `- ` prompt | yes (rustyline prompt) | yes (SML-NJ parity, written to output) | no | both front ends |
| `= ` continuation prompt | limited (see §6) | tty-only today | no | front end |
| banner | yes | yes | no | front end |
| echo | no | no | yes | `ScriptRunner` |
| idempotent `>`-lookahead, `output_matcher` | no | no | yes | `ScriptRunner` |
| history | yes | no | no | `Shell` |

Two subtleties:

* **Config is one bag, mutated at runtime.** `Sys.set("matchStrict", …)`
  changes a flag that the *runner* reads mid-loop. So `Config` stays
  owned by `Kernel`, and the runner queries it after each statement.
  Splitting the config struct is not worth doing in this pass.
* **Piped-interactive keeps `- ` prompts** (SML-NJ parity, covered by
  the `test_interactive_*` tests). Only the tty path migrates to
  rustyline; `ScriptRunner` keeps its prompt logic. This satisfies the
  issue's requirement that piped and scripted input behave as before,
  with zero risk to existing behavior.

## 5. Refactor before or after rustyline? Before — the data flow inverts

Today's loop pulls *bytes* through `R: Read` and assembles statements
itself. Rustyline hands the caller *complete statements*: its
`Validator` loops internally until the input validates. Wedging an
`Editor` behind `R: Read` would be upside-down — assembled statements
would be fed back through a byte stream just to be reassembled. So the
refactoring comes first, and rustyline lands as a purely additive front
end that touches no tested path.

The refactoring is mechanical and fully covered by the existing test
suite (the 60+ script tests plus `test_interactive_*`).

## 6. Plan

### Phase 1 — mechanical refactor (no behavior change)

* **R1.** Extract `shell/statement.rs`: move `comment_depth` there and
  add `is_complete(buf: &str) -> bool`. Use it from the `run` loop and
  `execute_use_file`. This removes existing triplication regardless of
  rustyline.
* **R2.** Split `shell/main.rs` into:
  * `shell/kernel.rs` — `Kernel`: the current `Shell` fields
    (config, environment, session, link_table), `process_statement`
    (consider renaming to `execute`), property get/set, `use`
    handling, `run_command`;
  * `shell/runner.rs` — `ScriptRunner`: the current `run<R, W>` loop
    (prompt/echo/idempotent), operating on `&mut Kernel`.

  Update the call sites: `src/main.rs`, `script_test.rs`, `wasm.rs`,
  and tests. `wasm.rs` becomes `MorelShell(Kernel)` — a naming
  improvement, since the wasm binding already used `Shell` as a kernel.
* **R3** (deferred). Config split into front-end vs. engine halves —
  skip; see §4.

Suggested commit: "Separate the kernel from the script runner".

### Phase 2 — rustyline front end (`Fixes #45`)

* `Cargo.toml`: add
  `rustyline = { version = "…", features = ["with-file-history"] }`
  under `[target.'cfg(not(target_arch = "wasm32"))'.dependencies]`.
  Rustyline does not build for wasm32; the Phase 1 split keeps the wasm
  build clean.
* `shell/terminal.rs`: new `Shell` holding an `Editor<MorelHelper>`
  and driving a `&mut Kernel`:
  * `MorelHelper` implements `Validator`: return
    `ValidationResult::Incomplete` while
    `!statement::is_complete(input)`. Rustyline then keeps extending a
    single buffer, so a multi-line statement is edited, submitted, and
    recorded in history as **one entry** — the issue's requirement 3
    falls out automatically.
  * History: `load_history`/`save_history` on `~/.morel_history`
    (resolve via `$HOME`; if unset, skip history rather than error).
  * Loop: `readline("- ")` →
    `Ok(stmt)` ⇒ `kernel.execute(…)`, print result;
    `Err(Interrupted)` (Ctrl-C) ⇒ discard buffer, fresh prompt;
    `Err(Eof)` (Ctrl-D) ⇒ "Goodbye!".
* `src/main.rs` dispatch: `stdin().is_terminal()` → rustyline `Shell`;
  otherwise → `ScriptRunner` exactly as today (the `--tty` plumbing
  already exists).
* Known cosmetic regression to accept: rustyline has no jline-style
  `SECONDARY_PROMPT_PATTERN`, so continuation lines will not show
  `= `. The issue already anticipates this (reedline migration is
  listed as a possible follow-up).
* Testing: the Validator's brain is `statement::is_complete`, which is
  unit-testable without a terminal; piped/script behavior is
  regression-covered by existing tests. True pty-based testing (the
  analogue of Morel-Java's `ShellTest`) via e.g. `rexpect` is a
  worthwhile follow-up, not a blocker.

### Phase 3 — follow-ups (out of scope, but anticipated by the design)

* `Completer` for tab-completion of environment bindings (see §7 for
  the snapshot pattern), `Highlighter` for syntax highlighting;
* reedline evaluation if richer multi-line editing is wanted;
* interrupting a *running* evaluation (Ctrl-C during a long query);
* pty-based shell test.

## 7. Rust's ownership model: challenges and opportunities

Mostly opportunities — the borrow checker *enforces* the separation this
plan proposes.

* **The basic loop has no borrow conflict.** `Editor` and `Kernel` are
  disjoint objects with strictly sequential borrows: read (mutates
  editor) → execute (mutates kernel) → print. Linear ownership; no new
  interior mutability. (`Rc<RefCell<Session>>` remains internal to the
  kernel, as today.)
* **Callbacks are where it would hurt — so they are not used.** A
  jline-ish design in which the line-reader's helper holds a reference
  into the engine is unwritable in safe Rust: the `Editor` owns the
  helper, and the helper cannot also borrow `&mut Kernel` across
  `readline`. Both consequences are good:
  * the `Validator` must be pure syntax — and it is
    (`is_complete` needs no engine state);
  * a future `Completer` cannot pull from the live environment;
    instead the loop *pushes a snapshot*
    (`editor.helper_mut().set_names(kernel.binding_names())`) after
    each statement. Cheaper and cleaner than a live callback, and it
    makes the completer trivially testable.
* **"Mutation while a command is executing."** The real instance is
  Ctrl-C during a long evaluation: a signal handler cannot touch the
  kernel while `execute(&mut self)` runs. The idiomatic answer is a
  cooperative `Arc<AtomicBool>` interrupt flag polled by the
  evaluator. Worth giving `Kernel` such a flag (one field) when it is
  created, implementing the polling later as its own issue —
  rustyline's `Interrupted` only covers Ctrl-C *at the prompt*.
* **wasm stays clean.** The kernel split keeps rustyline (and any
  terminal dependency) out of the wasm build via the target-specific
  dependency section.

## 8. Recommended sequence

1. R1 — `statement.rs` extraction (tiny; removes real duplication).
2. R2 — `Kernel`/`ScriptRunner` split (mechanical; verified by
   `fullMake`).
3. Rustyline front end per Phase 2 (`Fixes #45`).
4. File follow-up issues: pty-based shell test; `Completer` and
   `Highlighter`; Ctrl-C during evaluation; reedline evaluation.
