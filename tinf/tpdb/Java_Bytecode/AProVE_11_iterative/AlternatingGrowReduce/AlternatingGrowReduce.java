package AlternatingGrowReduce;

public class AlternatingGrowReduce {
	AlternatingGrowReduce next;

	public static void main(String[] argv) {
		Random.args = argv;
		AlternatingGrowReduce list = createList(Random.random());

		int mode = 0;
		while (list != null) {
			if (mode == 0) {
				list = list.next.next.next.next;
			} else if (mode == 1) {
				list = new AlternatingGrowReduce(list);
			} else if (mode > 1) {
				list = new AlternatingGrowReduce(new AlternatingGrowReduce(list));
			}

			mode++;
			if (mode > 2) {
				mode = 0;
			}
		}
	}

	public AlternatingGrowReduce(AlternatingGrowReduce old) {
		this.next = old;
	}

	public static AlternatingGrowReduce createList(int length) {
		AlternatingGrowReduce res = new AlternatingGrowReduce(null);
		while (length > 0) {
			res = new AlternatingGrowReduce(res);
			length--;
		}
		return res;
	}
}
