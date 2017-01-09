package ArrayPrimitives;

public class ArrayPrimitives {
	public static void main(String[] argv) {
		Random.args = argv;
		int int0 = Random.random();
		int int1 = Random.random();
		int int2 = Random.random();
		int[] data = {int0, int1, int2};
		while (data[0] != int0);
		while (data[1] != int1);
		while (data[2] != int2);
	}
}
