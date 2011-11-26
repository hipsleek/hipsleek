void run_infinite_on_neg(int x)
	case {
		x < 0 -> variance (-1) requires true ensures true;
		x >= 0 -> variance (0) requires true ensures true;
	}
{
	if (x < 0)
		run_infinite_on_neg(x);
}

void reduce_to_zero(int x)
	case {
		x < 0 -> variance [-x] requires true ensures true;
		x = 0 -> variance (0) requires true ensures true;
		x > 0 -> variance [x] requires true ensures true;
	}
{
	if (x < 0)
		reduce_to_zero(x + 1);
	else if (x > 0)
		reduce_to_zero(x - 1);
}
