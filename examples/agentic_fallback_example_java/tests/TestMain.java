import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.assertEquals;

public class TestMain {
    @Test
    public void testCreateUserGreeting() {
        assertEquals("Hello, John Doe!", Main.createUserGreeting());
    }
}
