import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

/**
 * This test verifies both the utility method behavior and that Main.main()
 * prints the expected sum to stdout. It intentionally fails to force the agent
 * to modify BOTH Main.java and Utils.java to make the project pass.
 *
 * Assumes JUnit 5 is available when the agent’s Java runner compiles/tests.
 * (When running via pdd with agentic fallback for non-Python, verification
 * may be skipped by default; this file still documents the intended behavior.)
 */
public class TestMain {

    private final PrintStream originalOut = System.out;
    private ByteArrayOutputStream out;

    @BeforeEach
    void setup() {
        out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out));
    }

    @AfterEach
    void teardown() {
        System.setOut(originalOut);
    }

    @Test
    void testUtilsAddReturnsFive() {
        // Should compile against Utils.add(int,int) and return 5.
        int result = Utils.add(2, 3);
        assertEquals(5, result, "Utils.add(2,3) must return 5");
    }

    @Test
    void testMainPrintsFive() {
        // Main should print the computed sum (5) followed by a newline.
        Main.main(new String[0]);
        String printed = out.toString().trim();
        assertEquals("5", printed, "Main.main should print 5");
    }
}
