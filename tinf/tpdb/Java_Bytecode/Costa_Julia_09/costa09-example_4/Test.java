package example_4;

/**
 * @costaContext example_4/Examples
 *
 */
public class Test {
	public void exampleMethods(ExamplesCont x, Examples y) {
		int i = 0;

		while (x.e.getF() > 0) {
			i += y.getF();
			x.e.setF(x.e.getF()-1);
		}
	}
	
	public static void main(String[] args) {
		Test o = new Test();
		ExamplesCont x = new ExamplesCont();
		Examples y = new Examples();
		o.exampleMethods(x,y);
	}
}
