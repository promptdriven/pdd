public class Main {
    public static void main(String[] args) {
        int result = testComputeSomething(0);
        System.out.println(result);
    }

    public static int testComputeSomething(int x) {
        return Util.add(x, 3);
    }
}
