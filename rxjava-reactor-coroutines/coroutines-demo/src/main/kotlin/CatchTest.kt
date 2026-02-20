import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking {
    println("Functional with catch:")
    flowOf(1, 2, 0, 4)
        .map { 10 / it }
        .catch { emit(-1) }
        .collect { println(it) }
    
    println("\nSequential try-catch inside (continues after error):")
    flow {
        flowOf(1, 2, 0, 4).collect { n ->
            try {
                emit(10 / n)
            } catch (e: ArithmeticException) {
                emit(-1)
            }
        }
    }.collect { println(it) }
    
    println("\nSequential - let it throw, catch outside (matches functional):")
    flow {
        flowOf(1, 2, 0, 4).collect { n ->
            emit(10 / n)
        }
    }.catch { emit(-1) }
     .collect { println(it) }
}
