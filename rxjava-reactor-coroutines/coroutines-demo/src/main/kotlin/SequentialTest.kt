import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking {
    println("=== Testing Sequential Flow Patterns ===")
    
    // 1. Basic - collect/emit
    println("\n1. Basic iteration:")
    flow {
        flowOf("Hello", "Coroutines", "World").collect { emit(it) }
    }.collect { println(it) }
    
    // 2. Map equivalent
    println("\n2. Map (uppercase):")
    flow {
        flowOf("apple", "banana", "cherry").collect { fruit ->
            emit(fruit.uppercase())
        }
    }.collect { println(it) }
    
    // 3. FlatMap equivalent
    println("\n3. FlatMap (split words):")
    flow {
        flowOf("Hi", "Rx").collect { word ->
            for (char in word) {
                emit(char.toString())
            }
        }
    }.collect { println(it) }
    
    // 4. Filter equivalent
    println("\n4. Filter (even numbers):")
    flow {
        (1..10).asFlow().collect { n ->
            if (n % 2 == 0) emit(n)
        }
    }.collect { println(it) }
    
    // 5. Reduce - need terminal anyway
    println("\n5. Reduce (sum 1-5):")
    var sum = 0
    (1..5).asFlow().collect { sum += it }
    println("Sum: $sum")
    
    // 6. Async calls
    println("\n6. Async (fetch user data):")
    flow {
        flowOf(1, 2, 3).collect { id ->
            delay(50)
            emit("User-$id")
        }
    }.collect { println(it) }
    
    // 7. Zip equivalent - trickier
    println("\n7. Zip (combine names and ages):")
    val names = listOf("Alice", "Bob")
    val ages = listOf(25, 30)
    flow {
        names.forEachIndexed { i, name ->
            emit("$name is ${ages[i]}")
        }
    }.collect { println(it) }
    
    // 8. Error handling
    println("\n8. Error handling:")
    flow {
        flowOf(1, 2, 0, 4).collect { n ->
            try {
                emit(10 / n)
            } catch (e: ArithmeticException) {
                emit(-1)
            }
        }
    }.collect { println(it) }
    
    println("\n=== Done ===")
}
