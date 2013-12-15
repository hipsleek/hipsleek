template int r(int n).

int mc91 (int n)
infer[r]
case {
	n>100 -> requires Term ensures res = n-10;
	n<=100 -> requires Term[100-n] ensures res = 91;
}
{
	if (n > 100) return n-10;
	else return mc91(mc91(n+11));
}

/*
# mc91.ss

why did we infer 900-9n instead of simpler 100-n?

why did the presence if infer[r] leads to:

# mc91-v.ss
Starting Omega...oc
trans_prog
WARNING (must fix): Vars from[r]has type UNK

*/
