import io.reactivex.rxjava3.core.*;
import java.util.concurrent.TimeUnit;

public class RxJavaDemo {
    public static void main(String[] args) throws InterruptedException {
        System.out.println("=== RxJava Demo ===");
        
        // 1. Basic Observable
        System.out.println("\n1. Basic Observable:");
        Observable.just("Hello", "RxJava", "World")
            .subscribe(System.out::println);
        
        // 2. Map
        System.out.println("\n2. Map (uppercase):");
        Observable.just("apple", "banana", "cherry")
            .map(String::toUpperCase)
            .subscribe(System.out::println);
        
        // 3. FlatMap - each item becomes a new Observable
        System.out.println("\n3. FlatMap (split words into chars):");
        Observable.just("Hi", "Rx")
            .flatMap(word -> Observable.fromArray(word.split("")))
            .subscribe(System.out::println);
        
        // 4. Filter
        System.out.println("\n4. Filter (even numbers):");
        Observable.range(1, 10)
            .filter(n -> n % 2 == 0)
            .subscribe(System.out::println);
        
        // 5. Reduce
        System.out.println("\n5. Reduce (sum 1-5):");
        Observable.range(1, 5)
            .reduce(0, Integer::sum)
            .subscribe(sum -> System.out.println("Sum: " + sum));
        
        // 6. FlatMap with async simulation
        System.out.println("\n6. FlatMap async (fetch user data):");
        Observable.just(1, 2, 3)
            .flatMap(RxJavaDemo::fetchUserAsync)
            .subscribe(System.out::println);
        
        // 7. Zip - combine streams
        System.out.println("\n7. Zip (combine names and ages):");
        Observable<String> names = Observable.just("Alice", "Bob");
        Observable<Integer> ages = Observable.just(25, 30);
        Observable.zip(names, ages, (name, age) -> name + " is " + age)
            .subscribe(System.out::println);
        
        // 8. Error handling
        System.out.println("\n8. Error handling:");
        Observable.just(1, 2, 0, 4)
            .map(n -> 10 / n)
            .onErrorReturnItem(-1)
            .subscribe(System.out::println);
        
        Thread.sleep(500); // Wait for async operations
    }
    
    static Observable<String> fetchUserAsync(int id) {
        return Observable.just("User-" + id)
            .delay(50, TimeUnit.MILLISECONDS);
    }
}
