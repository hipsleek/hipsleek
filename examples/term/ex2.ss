int foo (int x)

case {
	x <= 0 -> __Bot
	x > 0 ->
		case {
			x > 5 -> __May_Term
			x <= 5 -> __Must_Term
		}
}

case {
	x <= 0 -> __Bot
	x > 0 -> __May_Term
}


{
	if (x > 0) {
		if (x > 5) {
			if (randBool())
				return foo (x + 1);
			else
				return 0;
		}
		else
			return foo (x - 1);
	}
	else
		return 0;
}