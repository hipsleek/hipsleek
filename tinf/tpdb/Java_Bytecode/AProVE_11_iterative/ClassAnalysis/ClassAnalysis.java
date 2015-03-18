package ClassAnalysis;

public class ClassAnalysis {
	A field;

	public static void main(String[] args) {
		Random.args = args;
		ClassAnalysis t = new ClassAnalysis();
		t.field = new A();
		t.field = new B();
		t.eval();
	}

	public void eval() {
		int x = Random.random() % 100;
		this.field.test(x);
	}
}

class A {
	public boolean test(int x) {
		while (x > 0) {
			if (x > 10) {
				x--;
			} else {
				x++;
			}
		}
		return true;
	}
}

class B extends A {
	public boolean test(int x) {
		while (x > 0) {
			x--;
		}
		return true;
	}
}
