package example_1;

public class Test {

	public int add(int n,A o){
		int res=0;
		int i=0;
		while (i<=n){
			res=res+i;
			i=o.incr(i);
		}    
		return res;
	}

	public static void main(String[] args) {
		int test = 1000;
		Test testClass = new Test();
		A a = new A();
		int result1 = testClass.add(test,a);
		a = new B();
		int result2 = testClass.add(test,a);
		a = new C(); 
		int result3 = testClass.add(test,a);     
		// System.out.println("Result: "+result1 + result2 + result3);
	}
}
