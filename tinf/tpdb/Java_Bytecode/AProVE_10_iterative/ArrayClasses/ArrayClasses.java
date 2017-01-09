public class ArrayClasses {
	public static void main(String[] args) {
		Random.args = args;
		A[] data = new A[2];
		data[0] = new A();
		data[1] = new B();
		int i = Random.random();
		if (i == 1) data[i].method();
	}
}
