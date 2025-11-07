# Row Sink Integration Design

## Overview

Row sinks provide a push-based alternative to the current pull-based query evaluation in `Code::eval_from`. This document describes how to integrate them into the compilation and execution flow.

## Current Architecture (Pull-Based)

```
AST → Resolver → FromBuilder → Core::From → Code::From → eval_from()
                                                              ↓
                                                     QueryStep evaluation
                                                     (accumulate in vectors)
```

1. **Resolver** converts AST to Core using FromBuilder
2. **FromBuilder** optimizes and produces `Core::From` with steps
3. **Compiler** (not yet implemented in Rust) would convert `Core::From` to `Code::From`
4. **eval_from()** executes by accumulating intermediate results in vectors

## Proposed Architecture (Push-Based with Row Sinks)

```
AST → Resolver → FromBuilder → Core::From → Compiler → Code (with RowSink factory)
                                                           ↓
                                                    RowSink pipeline
                                                    (push rows downstream)
```

### Key Components

#### 1. Row Sink Factory Pattern

Following the Java implementation, use a **factory** that creates fresh row sink instances:

```rust
// In code.rs
pub enum Code {
    // ... existing variants ...

    /// FromRowSink(factory) evaluates a query using row sinks
    FromRowSink(Box<dyn Fn() -> Box<dyn RowSink>>),
}
```

**Why a factory?**
- Each query execution needs a fresh sink with cleared state
- Allows recursive queries without state pollution
- Matches the Java pattern: `Supplier<RowSink>`

#### 2. Compiler Integration

The Compiler (currently being developed) would have a method like:

```rust
impl Compiler {
    /// Compiles a Core::From expression into Code with row sinks
    fn compile_from(&mut self, from: &core::From) -> Code {
        let factory = self.create_row_sink_factory(
            &from.steps,
            &from.element_type
        );

        Code::FromRowSink(Box::new(move || {
            // Wrap with FirstRowSink to initialize all sinks
            Box::new(FirstRowSink::new(factory()))
        }))
    }

    /// Recursively builds row sink factory from steps
    fn create_row_sink_factory(
        &mut self,
        steps: &[core::FromStep],
        element_type: &Type,
    ) -> Box<dyn Fn() -> Box<dyn RowSink>> {
        if steps.is_empty() {
            // Terminal case: create CollectRowSink
            let code = self.get_field_code(element_type);
            return Box::new(move || {
                Box::new(CollectRowSink::new(code.clone()))
            });
        }

        let first_step = &steps[0];
        let next_factory = self.create_row_sink_factory(
            &steps[1..],
            element_type
        );

        match &first_step {
            core::FromStep::Scan { pat, expr, condition } => {
                let pat_code = self.compile_pattern(pat);
                let expr_code = self.compile(expr);
                let cond_code = self.compile(condition);

                Box::new(move || {
                    Box::new(ScanRowSink::new(
                        pat_code.clone(),
                        expr_code.clone(),
                        cond_code.clone(),
                        next_factory()
                    ))
                })
            }
            core::FromStep::Where { expr } => {
                let filter_code = self.compile(expr);

                Box::new(move || {
                    Box::new(WhereRowSink::new(
                        filter_code.clone(),
                        next_factory()
                    ))
                })
            }
            // ... other step types ...
        }
    }
}
```

#### 3. Evaluation

```rust
impl Code {
    pub fn eval_f0(&self, r: &mut EvalEnv, f: &mut Frame) -> Result<Val, MorelError> {
        match self {
            // ... existing cases ...

            Code::FromRowSink(factory) => {
                let mut sink = factory();
                sink.start(r, f)?;
                sink.accept(r, f)?;
                sink.result(r, f)
            }
        }
    }
}
```

## Execution Flow Example

For query: `from x in [1,2,3] where x > 1 yield x * 10`

### 1. Compilation Phase

```rust
// FromBuilder produces Core::From with steps:
// 1. Scan: x in [1,2,3]
// 2. Where: x > 1
// 3. (implicit) Yield: x * 10

// Compiler creates factory hierarchy:
factory = || {
    ScanRowSink {
        collection_code: Constant([1,2,3]),
        pat_code: BindSlot(x),
        condition_code: Constant(true),
        row_sink: WhereRowSink {
            filter_code: Apply(>, [GetLocal(x), Constant(1)]),
            row_sink: CollectRowSink {
                code: Apply(*, [GetLocal(x), Constant(10)])
            }
        }
    }
}
```

### 2. Execution Phase

```
1. Code::FromRowSink(factory).eval_f0(r, f)
2. Create sink = factory()
3. sink.start(r, f)
   - WhereRowSink.start() → CollectRowSink.start() → clear list
4. sink.accept(r, f)
   - ScanRowSink.accept():
     - Eval [1,2,3] → [1,2,3]
     - For each item:
       - item=1: bind x=1, condition=true, where filter: 1>1=false → skip
       - item=2: bind x=2, condition=true, where filter: 2>1=true → accept
         - CollectRowSink.accept(): eval x*10=20, add to list
       - item=3: bind x=3, condition=true, where filter: 3>1=true → accept
         - CollectRowSink.accept(): eval x*10=30, add to list
5. sink.result(r, f) → [20, 30]
```

## Migration Path

### Phase 5a (Current - Complete)
✅ Basic row sink infrastructure
- RowSink trait
- ScanRowSink, WhereRowSink, UnionRowSink, CollectRowSink

### Phase 5b (Next)
- [ ] Add `Code::FromRowSink` variant
- [ ] Add factory helpers in row_sink.rs
- [ ] Create simple test that manually constructs sink pipeline

### Phase 5c (After Compiler exists)
- [ ] Integrate with Compiler
- [ ] Add `compile_from()` method
- [ ] Replace `Code::From(QueryStep)` with `Code::FromRowSink`

### Phase 5d (Complete remaining sinks)
- [ ] GroupRowSink (aggregation)
- [ ] OrderRowSink (sorting)
- [ ] DistinctRowSink
- [ ] Skip/TakeRowSink (pagination)
- [ ] Join optimization (separate from scan)

## Benefits

1. **Memory efficiency**: Streaming instead of accumulating intermediate results
2. **Composability**: Sinks chain cleanly without coupling
3. **Testability**: Each sink can be tested independently
4. **Performance**: Eliminates vector allocations for intermediate steps
5. **Java compatibility**: Matches proven Java architecture

## Open Questions

1. **When does Compiler get implemented?** Row sinks need compilation support
2. **Pattern binding**: How to properly extend frame with pattern bindings?
3. **Variable scoping**: How to track which slots belong to which scope?
4. **Join semantics**: Should Join be separate from Scan or combined?

## Recommendation

For now, add factory support and manual construction tests in Phase 5b:

```rust
// In row_sink.rs, add helper:
pub fn create_simple_query(
    collection: Code,
    filter: Code,
    result: Code
) -> Box<dyn Fn() -> Box<dyn RowSink>> {
    Box::new(move || {
        Box::new(ScanRowSink::new(
            Code::BindWildcard, // accept all
            collection.clone(),
            Code::Constant(..., Val::Bool(true)), // no condition
            Box::new(WhereRowSink::new(
                filter.clone(),
                Box::new(CollectRowSink::new(result.clone()))
            ))
        ))
    })
}
```

This allows testing the architecture before full Compiler integration.
