# Query Translation to Core - Implementation Plan

This document outlines the plan for translating Standard ML queries (from/where/yield expressions) into Core representation in the Rust implementation of Morel.

## Overview

The query translation pipeline converts high-level relational syntax into executable Core expressions. This involves:

1. **FromBuilder** - Simplifies and optimizes query steps
2. **FromResolver** - Resolves variable references and scopes within queries
3. **AggregateResolver** - Handles aggregate operations (count, sum, etc.)
4. **StepEnv/FromStep** - Internal representations during query processing
5. **RowSink/RowSinks** - Pipeline execution model (separate from eager evaluation)

## Phase 1: FromBuilder Translation

**Status**: 🚧 In Progress (Foundation Complete)

**Java Source**: `/Users/jhyde/dev/morel.2/src/main/java/net/hydromatic/morel/ast/FromBuilder.java` (586 lines)

**Test Source**: `/Users/jhyde/dev/morel.2/src/test/java/net/hydromatic/morel/FromBuilderTest.java`

### Purpose
FromBuilder constructs and optimizes `Core.From` expressions by:
- Converting simple "from v in list" to just "list"
- Removing "where true" steps
- Removing empty "order" steps
- Removing trivial yield expressions
- Inlining nested from expressions

### Key Components
- Builder pattern with state tracking
- Step simplification rules
- Two build modes: `build()` and `buildSimplify()`
- Special handling for atom vs record results
- Index tracking for conditional step removal

### Translation Strategy
1. ✅ Add foundational types to `src/compile/core.rs`
2. 🚧 Create `src/compile/from_builder.rs`
3. ⏳ Translate FromBuilder class to struct with builder pattern
4. ⏳ Use `Vec<Step>` for steps collection
5. ⏳ Use `Option<usize>` for remove-if-last/not-last indices
6. ⏳ Write unit tests based on FromBuilderTest.java

### Rust Design Decisions
- Builder methods return `&mut Self` for chaining
- Use `Result<Expr, Error>` for build methods
- `clear()` method for builder reuse
- Type system integration via `TypeSystem` reference

### Progress Log

#### 2025-01-06: Foundation Complete (Commit 1777a8d)
- ✅ Added `Binding` struct to `src/compile/core.rs`
  - Tracks pattern bindings with `Id` and `Type`
  - Simplified from Java (no value/expression fields yet)
- ✅ Added `StepEnv` struct to `src/compile/core.rs`
  - Tracks bindings, atom flag, ordered flag at each query step
  - Methods: `empty()`, `new()`, `with_ordered()`, `with_bindings()`
- ✅ Extended `Step` to include `env: StepEnv` field
- ✅ Fixed compilation errors in `inliner.rs` and `resolver.rs`
- 🎯 Next: Create `from_builder.rs` module with FromBuilder struct

## Phase 2: FromResolver Translation

**Java Source**: `/Users/jhyde/dev/morel.2/src/main/java/net/hydromatic/morel/compile/Resolver.java` (FromResolver inner class, ~300 lines)

### Purpose
FromResolver is a visitor that:
- Resolves variable references within query expressions
- Manages variable scoping across query steps
- Converts AST from expressions to Core representations
- Handles pattern bindings in scan/join steps

### Key Components
- Visitor pattern for AST traversal
- Environment/scope management
- Pattern matching for step types
- Integration with AggregateResolver

### Translation Strategy
1. Add to `src/compile/resolver.rs` or create `src/compile/from_resolver.rs`
2. Use visitor pattern (trait implementation)
3. Integrate with existing Resolver struct
4. Coordinate with TypeResolver for type information

### Rust Design Decisions
- Trait-based visitor vs match-based dispatcher
- Environment as immutable with builder pattern for new scopes
- Use Rc/Arc for shared environment references

## Phase 3: AggregateResolver Translation

**Java Source**: `/Users/jhyde/dev/morel.2/src/main/java/net/hydromatic/morel/compile/Resolver.java` (AggregateResolverImpl, plus subclasses)

### Purpose
Handles aggregate operations in queries:
- Resolves aggregate functions (count, sum, avg, etc.)
- Manages group-by semantics
- Handles the `elements` keyword in compute clauses
- Coordinates with FromResolver for variable scoping

### Challenges
- Java uses subclasses for different aggregate types
- Multiple implementations: AggregateResolverImpl, GroupAggregateResolver, etc.
- Polymorphic behavior via inheritance

### Translation Strategy (Options)

**Option A: Trait Objects (`dyn AggregateResolver`)**
```rust
trait AggregateResolver {
    fn resolve_aggregate(&self, expr: &Expr) -> Result<Core, Error>;
    fn get_elements(&self) -> Option<Core>;
}

struct AggregateResolverImpl { /* ... */ }
struct GroupAggregateResolver { /* ... */ }

impl AggregateResolver for AggregateResolverImpl { /* ... */ }
impl AggregateResolver for GroupAggregateResolver { /* ... */ }

// Usage: Box<dyn AggregateResolver>
```

**Option B: Enum Dispatch**
```rust
enum AggregateResolver {
    Base(AggregateResolverImpl),
    Group(GroupAggregateResolver),
    // Other variants...
}

impl AggregateResolver {
    fn resolve_aggregate(&self, expr: &Expr) -> Result<Core, Error> {
        match self {
            AggregateResolver::Base(r) => r.resolve_aggregate(expr),
            AggregateResolver::Group(r) => r.resolve_aggregate(expr),
        }
    }
}
```

**Recommendation**: Use **trait objects** (`Box<dyn AggregateResolver>`) for flexibility and extensibility, matching Java's polymorphic design.

### Rust Design Decisions
- `dyn AggregateResolver` for polymorphism
- Separate module: `src/compile/aggregate_resolver.rs`
- Builder pattern for constructing different resolver types

## Phase 4: StepEnv and FromStep

**Java Source**: Classes within Resolver.java

### Purpose
Internal representations used during query resolution:
- **StepEnv**: Tracks variable bindings and types at each step
- **FromStep**: Intermediate representation of query steps during compilation

### Questions
- Are these needed in Rust, or can we use different intermediate structures?
- Can we leverage Rust's type system to eliminate some bookkeeping?

### Translation Strategy
1. Analyze usage patterns in Java code
2. Determine if direct translation is needed or if Rust idioms allow simplification
3. Consider using builder pattern state instead of separate types

## Phase 5: RowSink and Pipeline Execution

**Java Source**:
- `/Users/jhyde/dev/morel.2/src/main/java/net/hydromatic/morel/eval/RowSink.java`
- Related RowSinks utilities

### Purpose
Pipeline-based execution model for queries:
- Alternative to eager (materialized) evaluation
- Streaming execution for large datasets
- Push-based data flow

### Key Concepts
- **RowSink**: Receiver interface for row-by-row data
- **RowSinks**: Factory and utility methods
- Different from the existing eager evaluation in `src/eval/`

### Translation Strategy
1. Create separate module: `src/eval/pipeline/`
2. Define `RowSink` trait
3. Implement various sink types (collector, filter, etc.)
4. Keep separate from eager evaluation model
5. Integration point with FromBuilder's compiled output

### Rust Design Decisions
- Trait-based design: `trait RowSink<T>`
- Generic over row types
- Potentially use iterators/streams instead of push model
- Consider `async` for streaming in future

## Implementation Order

1. **Phase 1: FromBuilder** (First, foundational)
   - Translate FromBuilder.java
   - Translate FromBuilderTest.java
   - ~1-2 weeks

2. **Phase 2: FromResolver** (Depends on FromBuilder)
   - Integrate with existing Resolver
   - ~1 week

3. **Phase 3: AggregateResolver** (Parallel with FromResolver)
   - Design trait hierarchy
   - Implement base and specialized resolvers
   - ~1-2 weeks

4. **Phase 4: StepEnv/FromStep** (As needed)
   - Determine necessity during Phases 2-3
   - Implement if needed
   - ~3-5 days

5. **Phase 5: RowSink/Pipeline** (Later, separate track)
   - Can be done independently
   - Start after Phases 1-3 complete
   - ~1-2 weeks

## Open Questions

1. **Memory Management**: How to handle shared references to environments and type information?
   - Likely answer: Use `Rc` for immutable sharing, `Arc` if threading needed

2. **Error Handling**: Consistent error type across all phases?
   - Extend existing `Error` enum in `src/shell/error.rs`?
   - Or create `QueryCompileError` type?

3. **Integration Points**: How does this fit with existing compilation pipeline?
   - Current: Parser → TypeResolver → Compiler → Code
   - New: Parser → TypeResolver → **FromBuilder/Resolver** → Compiler → Code

4. **Testing Strategy**:
   - Unit tests per module (translate Java tests)
   - Integration tests with full query pipeline
   - Property-based tests for optimization equivalence?

5. **Performance**: Are the Java optimizations (like step removal) necessary in Rust?
   - May be able to rely on LLVM optimizations
   - Or introduce different optimization passes

## Success Criteria

- [ ] FromBuilder translates and all tests pass
- [ ] FromResolver integrates with existing Resolver
- [ ] AggregateResolver handles group-by and aggregates correctly
- [ ] Query expressions compile to correct Core representation
- [ ] Pipeline execution model (RowSink) implemented
- [ ] Performance comparable to or better than Java implementation
- [ ] All existing query tests continue to pass

## References

- Java FromBuilder: `morel.2/src/main/java/net/hydromatic/morel/ast/FromBuilder.java`
- Java Resolver: `morel.2/src/main/java/net/hydromatic/morel/compile/Resolver.java`
- Java RowSink: `morel.2/src/main/java/net/hydromatic/morel/eval/RowSink.java`
- Rust Core types: `src/compile/core.rs`
- Rust AST: `src/syntax/ast.rs`
