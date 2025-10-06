public class Main {
    public static void main(String[] args) {
        // Intentionally relies on Utils.add(int, int), but Utils.java is wrong.
        int result = Utils.add(2, 3);
        System.out.println(result);
    }
}