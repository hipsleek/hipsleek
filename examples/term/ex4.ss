int f (int x)

case {
	x >= 0 -> T1
	x < 0 -> __Bot
}

{
	if (x >= 0)
		return 1 + g(x - 1);
	else
		return 0;
}

int g (int x)

case {
	x >= 0 -> T2
	x < 0 -> __Bot
}

{
	if (x >= 0)
		return 2 + f(x);
	else
		return 0;
}

T2 = x >= 0 &
     case {x >= 0 -> T1;
		   x < 0 -> __Bot}
   = case {x >= 0 -> T1} (MUST)

T2(>=0) = T1(>=0) (1)

T1 = x >= 0 & 
     case {x-1 >= 0 -> T2;
		   x-1 < 0 -> __Bot} (MAY)
   = case {x >= 1 -> T2
		   x = 0 -> __Bot}

T1(>=1) = T2(>=0) (2)
T1(=0) = __Bot    (3)

(1)+(2): T1(>=1) = T1(>=0)
         T1(=0)  = __Bot