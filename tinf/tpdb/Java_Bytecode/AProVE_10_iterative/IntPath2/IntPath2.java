public class IntPath2 {
    public static void main(String[] args) {
        Random.args = args;
		Object obj = null;
        int i = Random.random();
		if (i > 0)
			obj = new Object();
		while (i == 0 && obj != null)
			obj = new Object();
    }
}
