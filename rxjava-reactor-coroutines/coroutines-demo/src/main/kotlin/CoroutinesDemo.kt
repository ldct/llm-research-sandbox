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
    
    // 1. Basic iteration
    println("\n1. Basic iteration:")
    for (item in listOf("Hello", "Coroutines", "World")) {
        println(item)
    }
    
    // 2. Map with loop
    println("\n2. Map (uppercase):")
    for (fruit in listOf("apple", "banana", "cherry")) {
        println(fruit.uppercase())
    }
    
    // 3. FlatMap with nested loops
    println("\n3. FlatMap (split words):")
    for (word in listOf("Hi", "Rx")) {
        for (char in word) {
            println(char)
        }
    }
    
    // 4. Filter with if
    println("\n4. Filter (even numbers):")
    for (n in 1..10) {
        if (n % 2 == 0) println(n)
    }
    
    // 5. Reduce with accumulator
    println("\n5. Reduce (sum 1-5):")
    var sumSeq = 0
    for (n in 1..5) {
        sumSeq += n
    }
    println("Sum: $sumSeq")
    
    // 6. Async with sequential calls
    println("\n6. Sequential async (fetch user data):")
    for (id in 1..3) {
        val user = fetchUser(id)
        println(user)
    }
    
    // 7. Zip with indexed iteration
    println("\n7. Zip (combine names and ages):")
    val namesList = listOf("Alice", "Bob")
    val agesList = listOf(25, 30)
    for (i in namesList.indices) {
        println("${namesList[i]} is ${agesList[i]}")
    }
    
    // 8. Error handling with try-catch
    println("\n8. Error handling:")
    for (n in listOf(1, 2, 0, 4)) {
        try {
            println(10 / n)
        } catch (e: Exception) {
            println(-1)
            break
        }
    }
    
    // 9. Parallel with async/await
    println("\n9. Parallel execution:")
    coroutineScope {
        val a = async { fetchData("A", 100) }
        val b = async { fetchData("B", 50) }
        println("${a.await()}, ${b.await()}")
    }
}

fun fetchUserFlow(id: Int): Flow<String> = flow {
    delay(50)
    emit("User-$id")
}

suspend fun fetchUser(id: Int): String {
    delay(50)
    return "User-$id"
}

suspend fun fetchData(name: String, delayMs: Long): String {
    delay(delayMs)
    return "Data-$name"
}
