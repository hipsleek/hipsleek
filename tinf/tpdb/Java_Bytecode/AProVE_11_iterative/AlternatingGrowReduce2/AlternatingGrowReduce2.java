package AlternatingGrowReduce2;

public class AlternatingGrowReduce2 {
	AlternatingGrowReduce2 next;

	public static void main(String[] argv) {
		Random.args = argv;
		AlternatingGrowReduce2 list = createList(Random.random());

		int mode = 0;
		while (list != null) {
			if (mode == 0) {
				list = list.next;
			} else if (mode == 1) {
				list = new AlternatingGrowReduce2(list);
			} else if (mode > 1) {
				list = list.next;
			}

			mode++;
			if (mode > 2) {
				mode = 0;
			}
		}
	}

	public AlternatingGrowReduce2(AlternatingGrowReduce2 old) {
		this.next = old;
	}

	public static AlternatingGrowReduce2 createList(int length) {
		AlternatingGrowReduce2 res = new AlternatingGrowReduce2(null);
		while (length > 0) {
			res = new AlternatingGrowReduce2(res);
			length--;
		}
		return res;
	}
}
