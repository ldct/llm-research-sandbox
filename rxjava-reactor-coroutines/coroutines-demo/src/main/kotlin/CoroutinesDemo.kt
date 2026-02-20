import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking {
    println("=== Kotlin Coroutines Demo ===")
    println("=== Functional (Flow) Style ===")
    
    // 1. Basic Flow
    println("\n1. Basic Flow:")
    flowOf("Hello", "Coroutines", "World")
        .collect { println(it) }
    
    // 2. Flow map
    println("\n2. Flow map (uppercase):")
    flowOf("apple", "banana", "cherry")
        .map { it.uppercase() }
        .collect { println(it) }
    
    // 3. FlatMapConcat (like flatMap)
    println("\n3. FlatMapConcat (split words):")
    flowOf("Hi", "Rx")
        .flatMapConcat { word -> word.toList().asFlow().map { it.toString() } }
        .collect { println(it) }
    
    // 4. Filter
    println("\n4. Filter (even numbers):")
    (1..10).asFlow()
        .filter { it % 2 == 0 }
        .collect { println(it) }
    
    // 5. Reduce
    println("\n5. Reduce (sum 1-5):")
    val sum = (1..5).asFlow().reduce { a, b -> a + b }
    println("Sum: $sum")
    
    // 6. FlatMapMerge with async
    println("\n6. FlatMapMerge async (fetch user data):")
    flowOf(1, 2, 3)
        .flatMapConcat { fetchUserFlow(it) }
        .collect { println(it) }
    
    // 7. Zip flows
    println("\n7. Zip (combine names and ages):")
    val names = flowOf("Alice", "Bob")
    val ages = flowOf(25, 30)
    names.zip(ages) { name, age -> "$name is $age" }
        .collect { println(it) }
    
    // 8. Error handling
    println("\n8. Error handling:")
    flowOf(1, 2, 0, 4)
        .map { 10 / it }
        .catch { emit(-1) }
        .collect { println(it) }
    
    // 9. Parallel with Flow
    println("\n9. Parallel execution (Flow):")
    val resultFlow = flow {
        coroutineScope {
            val a = async { fetchData("A", 100) }
            val b = async { fetchData("B", 50) }
            emit("${a.await()}, ${b.await()}")
        }
    }
    resultFlow.collect { println(it) }

    println("\n" + "=".repeat(50))
    println("=== Sequential (Imperative) Style ===")
    println("(Using flow { collect { emit() } } pattern)")
    
    // 1. Basic - collect/emit passthrough
    println("\n1. Basic iteration:")
    flow {
        flowOf("Hello", "Coroutines", "World").collect { emit(it) }
    }.collect { println(it) }
    
    // 2. Map with collect/emit
    println("\n2. Map (uppercase):")
    flow {
        flowOf("apple", "banana", "cherry").collect { fruit ->
            emit(fruit.uppercase())
        }
    }.collect { println(it) }
    
    // 3. FlatMap with nested emit
    println("\n3. FlatMap (split words):")
    flow {
        flowOf("Hi", "Rx").collect { word ->
            for (char in word) {
                emit(char.toString())
            }
        }
    }.collect { println(it) }
    
    // 4. Filter with if + emit
    println("\n4. Filter (even numbers):")
    flow {
        (1..10).asFlow().collect { n ->
            if (n % 2 == 0) emit(n)
        }
    }.collect { println(it) }
    
    // 5. Reduce with accumulator in collect
    println("\n5. Reduce (sum 1-5):")
    var sumSeq = 0
    (1..5).asFlow().collect { sumSeq += it }
    println("Sum: $sumSeq")
    
    // 6. Async with delay in collect/emit
    println("\n6. Sequential async (fetch user data):")
    flow {
        flowOf(1, 2, 3).collect { id ->
            delay(50)
            emit("User-$id")
        }
    }.collect { println(it) }
    
    // 7. Zip - collect both flows, combine
    println("\n7. Zip (combine names and ages):")
    flow {
        val namesList = flowOf("Alice", "Bob").toList()
        val agesList = flowOf(25, 30).toList()
        namesList.forEachIndexed { i, name ->
            emit("$name is ${agesList[i]}")
        }
    }.collect { println(it) }
    
    // 8. Error handling - let it throw, catch outside
    println("\n8. Error handling:")
    flow {
        flowOf(1, 2, 0, 4).collect { n ->
            emit(10 / n)
        }
    }.catch { emit(-1) }
     .collect { println(it) }
    
    // 9. Parallel with async/await inside flow
    println("\n9. Parallel execution:")
    flow {
        coroutineScope {
            val a = async { fetchData("A", 100) }
            val b = async { fetchData("B", 50) }
            emit("${a.await()}, ${b.await()}")
        }
    }.collect { println(it) }
}

fun fetchUserFlow(id: Int): Flow<String> = flow {
    delay(50)
    emit("User-$id")
}

suspend fun fetchData(name: String, delayMs: Long): String {
    delay(delayMs)
    return "Data-$name"
}
