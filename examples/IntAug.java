final class IntAug {
	public boolean  bound;
	public int   val;

	IntAug() {
		bound = false;
		val = 0;
	}

	IntAug(int p) {
		val = p;
		bound = true;
	}

	IntAug(IntAug p) {
		val = p.val;
		bound = p.bound;
	}

	public static final int min(int a, int b) {
		return a < b ? a : b;
	}

	public static final int min(IntAug a, int b) {
		if (a.bound) {
			return a.val < b ? a.val : b;
		}
		else {
			a.bound = true;
			a.val = (int)(((double)Integer.MAX_VALUE) * Math.random());
			return a.val < b ? a.val : b;
		}
	}

	public static final int min(int a, IntAug b) {
		if (b.bound) {
			return a < b.val ? a : b.val;
		}
		else {
			b.bound = true;
			b.val = (int)(((double)Integer.MAX_VALUE) * Math.random());
			return a < b.val ? a : b.val;
		}
	}

	public static final int max(int a, int b) {
		return a > b ? a : b;
	}
	
	final boolean EQ(int p) {
		if (bound) return val == p;
		val = p;
		return true;
	}

	final boolean EQ(IntAug p) {
		if (bound && p.bound) return val == p.val;
		if (bound && !p.bound) {
			p.bound = true;
			p.val = val;
			return true;
		}
		if (!bound && p.bound) {
			bound = true;
			val = p.val;
			return true;
		}
		val = (int) (((double)Integer.MAX_VALUE) * Math.random());
		p.val = val;
		bound = true;
		p.bound = true;
		return true;
	}

	final boolean LTE(int p) {
		if (bound) return val <= p;
		val = (int) (((double)p) * Math.random());
		return true;
	}

	final boolean LTE(IntAug p) {
		if (bound && p.bound) return val <= p.val;
		if (bound && !p.bound) {
			p.bound = true;
			p.val = (int)(((double)val) / Math.random());
			return true;
		}
		if (!bound && p.bound) {
			bound = true;
			val = (int)(((double)p.val) * Math.random());
			return true;
		}

		bound = true;
		p.bound = true;
		val = (int) (((double)Integer.MAX_VALUE) * Math.random());
		p.val = (int)(((double)val) / Math.random());
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
