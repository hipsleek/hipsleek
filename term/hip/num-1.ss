int f (int x)
/*
case {
	x<=0 -> requires Term[1,0] ensures res=0;
  x>0 -> requires Term[1,1] ensures res=2+x;
}
*/

case {
	x<=0 -> requires Term[] ensures res=0;
  x>0 -> requires Term[] ensures res=2+x;
}

{
	if (x>0) {
		return 1+g(x);
	}
  else {
		return 0;
	}
}

int g (int x)
/*
case {
	x<0 -> requires Term[0,0] ensures res=0;
  x>=0 -> requires Term[0,1,x] ensures res=1+x;
}
*/

case {
	x<0 -> requires Term[] ensures res=0;
  x>=0 -> requires Term[x] ensures res=1+x;
}

{
	if (x>=0) {
		return 1+g(x-1);
	} 
  else {
		return 0;
  }
}
