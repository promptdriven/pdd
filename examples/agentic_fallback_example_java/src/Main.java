public class Main {
    public static String createUserGreeting() {
        return Utils.getGreeting("John", "Doe");
    }

    public static void main(String[] args) {
        System.out.println(createUserGreeting());
    }
}