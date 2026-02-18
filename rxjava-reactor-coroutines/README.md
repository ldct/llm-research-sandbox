# Reactive/Async Java & Kotlin Comparison

A minimal side-by-side comparison of RxJava, Project Reactor, and Kotlin Coroutines, demonstrating equivalent patterns across all three paradigms.

## Project Structure

```
.
├── rxjava-demo/           # Java + RxJava 3 examples
│   └── src/main/java/RxJavaDemo.java
├── reactor-demo/          # Java + Project Reactor examples
│   └── src/main/java/ReactorDemo.java
├── coroutines-demo/       # Kotlin Coroutines examples
│   └── src/main/kotlin/CoroutinesDemo.kt
└── website/               # Static HTML comparison site
    └── index.html
```

## Dependencies

All projects are intentionally minimal:

| Project | Dependency | Version |
|---------|------------|--------|
| rxjava-demo | `io.reactivex.rxjava3:rxjava` | 3.1.8 |
| reactor-demo | `io.projectreactor:reactor-core` | 3.6.0 |
| coroutines-demo | `org.jetbrains.kotlinx:kotlinx-coroutines-core` | 1.8.0 |

No UI libraries, no Android, no Spring - just the core reactive/async libraries.

## Building & Running

### Prerequisites

- Java 21+
- Gradle (or use the included wrapper)

### RxJava Demo

```bash
cd rxjava-demo
./gradlew run --quiet
```

### Reactor Demo

```bash
cd reactor-demo
./gradlew run --quiet
```

### Coroutines Demo

```bash
cd coroutines-demo
./gradlew run --quiet
```

## Examples Covered

All demos cover these patterns with identical output:

| # | Pattern | RxJava | Project Reactor | Coroutines (Flow) | Coroutines (Sequential) |
|---|---------|--------|-----------------|-------------------|-------------------------|
| 1 | Stream creation | `Observable.just()` | `Flux.just()` | `flowOf()` | `for` loop |
| 2 | Transform | `map()` | `map()` | `map {}` | inline in loop |
| 3 | Flatten | `flatMap()` | `flatMap()` | `flatMapConcat {}` | nested loops |
| 4 | Filter | `filter()` | `filter()` | `filter {}` | `if` statement |
| 5 | Aggregate | `reduce()` | `reduce()` | `reduce {}` | accumulator variable |
| 6 | Async calls | `flatMap()` + `delay()` | `flatMap()` + `delayElement()` | `flatMapConcat {}` + `delay()` | `suspend fun` in loop |
| 7 | Combine streams | `zip()` | `zip()` | `zip()` | indexed iteration |
| 8 | Error handling | `onErrorReturnItem()` | `onErrorReturn()` | `catch {}` | `try/catch` |

## Key Differences

### RxJava
- Everything is a stream (`Observable`, `Single`, `Maybe`, `Flowable`)
- Operators are chained declaratively
- Backpressure handling with `Flowable`
- Schedulers for threading (`Schedulers.io()`, `Schedulers.computation()`)

### Project Reactor
- Two main types: `Mono<T>` (0-1 items) and `Flux<T>` (0-N items)
- Native Reactive Streams implementation (same as RxJava 3)
- Foundation for Spring WebFlux
- Schedulers: `Schedulers.boundedElastic()`, `Schedulers.parallel()`

### Kotlin Coroutines
- **Flow style**: Similar to RxJava, chain operators on `Flow<T>`
- **Sequential style**: Write async code like sync code using `suspend` functions
- Structured concurrency with `coroutineScope`
- No backpressure by default (Flow is cold and sequential)

### When to use which style in Kotlin?

| Use Flow when... | Use Sequential when... |
|------------------|------------------------|
| You need reactive streams semantics | You're doing simple async operations |
| Multiple collectors need the same stream | One-shot operations |
| You want operators like `debounce`, `distinctUntilChanged` | Sequential steps are clearer |
| Interop with RxJava via `asFlow()`/`asObservable()` | You prefer imperative style |

## Website

A static HTML page showing all examples side-by-side with syntax highlighting.

### Run locally

```bash
cd website
busybox httpd -f -p 8000 -h .
# Or
python -m http.server 8000
```

Then open http://localhost:8000

### Live version

https://rxjava-coroutine-comparison.exe.xyz:8000/

## Adding New Examples

1. Add the RxJava code to `rxjava-demo/src/main/java/RxJavaDemo.java`
2. Add the Reactor code to `reactor-demo/src/main/java/ReactorDemo.java`
3. Add both Flow and Sequential versions to `coroutines-demo/src/main/kotlin/CoroutinesDemo.kt`
4. Run all three to verify identical output
5. Add a new `<div class="comparison">` block to `website/index.html`

## References

- [RxJava 3 Wiki](https://github.com/ReactiveX/RxJava/wiki)
- [Project Reactor Reference](https://projectreactor.io/docs/core/release/reference/)
- [Kotlin Coroutines Guide](https://kotlinlang.org/docs/coroutines-guide.html)
- [Kotlin Flow Documentation](https://kotlinlang.org/docs/flow.html)
- [Migrating from RxJava to Coroutines](https://developer.android.com/kotlin/coroutines/coroutines-rxjava)
