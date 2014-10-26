/**
 * Based on union-find data structures with a self-loop as sentinel,
 * as presented on
 * http://en.wikipedia.org/w/index.php?title=Disjoint-set_data_structure&oldid=558948590
 *
 * Non-recursive version.
 */
public class UnionFindIterative {
    private UnionFindIterative parent;

    public UnionFindIterative(UnionFindIterative parent) {
        this.parent = parent;
    }

    public void makeSet() {
        this.parent = this;
    }

    /**
     * Here you need to know about this that the only panhandle list
     * you can possibly reach from this has a "pan" which is a self-loop.
     */
    public UnionFindIterative find() {
        UnionFindIterative candidate = this;
        while (candidate.parent != candidate) {
            candidate = candidate.parent;
        }
        return candidate;
    }

    public void union(UnionFindIterative y) {
        UnionFindIterative xRoot = this.find();
        UnionFindIterative yRoot = y.find();
        xRoot.parent = yRoot;
    }

    public static void main(String[] args) {
        UnionFindIterative y = new UnionFindIterative(null);
        y.makeSet();
        for (int i = 0; i < args[0].length(); ++i) {
            UnionFindIterative x = new UnionFindIterative(null);
            x.makeSet();
            x.union(y);
        }
    }
}
