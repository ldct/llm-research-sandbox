import reactor.core.publisher.*;
import java.time.Duration;

public class ReactorDemo {
    public static void main(String[] args) throws InterruptedException {
        System.out.println("=== Reactor Demo ===");
        
        // 1. Basic Flux
        System.out.println("\n1. Basic Flux:");
        Flux.just("Hello", "Reactor", "World")
            .subscribe(System.out::println);
        
        // 2. Map
        System.out.println("\n2. Map (uppercase):");
        Flux.just("apple", "banana", "cherry")
            .map(String::toUpperCase)
            .subscribe(System.out::println);
        
        // 3. FlatMap - each item becomes a new Flux
        System.out.println("\n3. FlatMap (split words into chars):");
        Flux.just("Hi", "Rx")
            .flatMap(word -> Flux.fromArray(word.split("")))
            .subscribe(System.out::println);
        
        // 4. Filter
        System.out.println("\n4. Filter (even numbers):");
        Flux.range(1, 10)
            .filter(n -> n % 2 == 0)
            .subscribe(System.out::println);
        
        // 5. Reduce
        System.out.println("\n5. Reduce (sum 1-5):");
        Flux.range(1, 5)
            .reduce(0, Integer::sum)
            .subscribe(sum -> System.out.println("Sum: " + sum));
        
        // 6. FlatMap with async simulation
        System.out.println("\n6. FlatMap async (fetch user data):");
        Flux.just(1, 2, 3)
            .flatMap(ReactorDemo::fetchUserAsync)
            .subscribe(System.out::println);
        
        // 7. Zip - combine streams
        System.out.println("\n7. Zip (combine names and ages):");
        Flux<String> names = Flux.just("Alice", "Bob");
        Flux<Integer> ages = Flux.just(25, 30);
        Flux.zip(names, ages, (name, age) -> name + " is " + age)
            .subscribe(System.out::println);
        
        // 8. Error handling
        System.out.println("\n8. Error handling:");
        Flux.just(1, 2, 0, 4)
            .map(n -> 10 / n)
            .onErrorReturn(-1)
            .subscribe(System.out::println);
        
        Thread.sleep(500); // Wait for async operations
    }
    
    static Mono<String> fetchUserAsync(int id) {
        return Mono.just("User-" + id)
            .delayElement(Duration.ofMillis(50));
    }
}
