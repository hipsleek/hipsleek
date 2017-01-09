// McCarthy 91
int f(int x)
requires true
ensures true;
{
	int s = 1;
	return loop(x, s);
}

int loop(int x, int s)
requires s>=1
//variance [0,1,10*s-x+90,x]
case {
  //Lexicographical ranking function <10s-x+90,x>
  x>100 -> case {
	   s=1 -> ensures "l1":true;
	   s!=1 -> //variance x
		  ensures "l2":true;
	  }
  x<=100 -> //variance 10s-x
	  ensures "l3":true;
}
{
	int x1, s1;
	if (x > 100) {
		if (s == 1) return x - 10;
		else {
			x1 = x - 10;
			s1 = s - 1;
			assert "l2": (10*s1'-x1'+90)-(10*s'-x'+90) = 0;
			assert "l2": (x1'-x')<0;
			assert "l2": x1'>=0;
			assert "l2": x'>=0;
			return loop(x1, s1);
		}
	} else {
		x1 = x + 11;
		s1 = s + 1;

		//assert "l3": (10*s1'-x1')-(10*s'-x') < 0;
		//assert "l3": (10*s1'-x1')>=-91;
		assert "l3": (10*s1'-x1'+90)-(10*s'-x'+90) < 0;
		assert "l3": (10*s'-x'+90)>=0;
		return loop(x1, s1);
	}
}
