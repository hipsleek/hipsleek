public class Init {

    public void m() {
	new A();
    }

    public void n() {
	A.f = 13;
    }

    public static void main(String[] args) {
	new Init().m();
	new Init().n();
    }
}