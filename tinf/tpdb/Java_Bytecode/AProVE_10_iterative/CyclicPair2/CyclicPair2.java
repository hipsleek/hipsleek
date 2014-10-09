public class CyclicPair2 {
	CyclicPair2 next;

    public static void main(String[] args) {
        Random.args = args;
        CyclicPair2 one = new CyclicPair2();
        CyclicPair2 two = new CyclicPair2();
		int rand = Random.random();
        if (rand != 0) {
            one.next = two;
            two.next = one;
        } else {
            one.next = two;
        }

        if (rand == 0) {
            one.run();
        }
    }

    public void run() {
       CyclicPair2 current = this;
       while (current != null)
           current = current.next;
    }
}
