data snode {
	int d;
	snode s;
	snode n;
}

skip0<e> == self = e
	or self::snode<d, s, n> * n::skip0<e> & s = null;

skip1<> == self = null
	or self::snode<d, s, n> * s::skip1<> * n::skip0<s>;

void rebalance(
