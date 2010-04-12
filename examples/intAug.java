final class intAug {
	public boolean  bound;
	public int   val;
	
	final boolean EQ(int p) {
		if (bound) return val == p;
		val = p;
		return true;
	}

	final boolean LTE(int p) {
		if (bound) return val <= p;
		val = (int) (((double)p) * Math.random());
		return true;
	}

	final boolean LT(int p) {
		if (bound) return val < p;
		val = (int) (((double)(p - 1)) * Math.random());
		return true;
	}

	final boolean GTE(int p) {
		if (bound) return val >= p;
		val = (int) (((double)p) / Math.random());
		return true;
	}

	final boolean GT(int p) {
		if (bound) return val > p;
		val = (int) (((double)(p + 1)) / Math.random());
		return true;
	}
}