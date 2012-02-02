/*
checkentail c=1 & x<=100 & Term[]
 & x'=x+11 & c'=c+1 |- Term[]. 

checkentail c>1 & x>100 & Term[]
 & x'=x-10 & c'=c-1 |- Term[]. 

checkentail c>1 & x<=100 & Term[]
 & x'=x+10 & c'=c+1 |- Term[]. 
*/

int mcCarthy (int x)
requires x<=111
case {
	x>100 -> ensures res=x-10;
	x<=100 -> ensures res=91;
}
{
	int c = 1;
	loop(x, c);
	return x;
}

    /*
      case {
      x>100 -> requires MayLoop ensures x'=91 & c'=0 ;
      x<=100 -> requires MayLoop ensures x'=91 & c'=0 ;
	 }
    */
void loop (ref int x, ref int c)
requires x<=111
case {
	c<=0 -> requires Term[] ensures x'=x & c'=c ;
    /*    c=1 ->
      case {
		x>100 -> requires Term[] ensures x'=x-10 & c'=0 ;

		x<=100 -> requires MayLoop ensures x'=91 & c'=0 ;
        }*/
    c>=1 -> 
 case {
      x>100 -> requires Term[1,x]  ensures true;
      x<=100 -> requires Term[1,111-x] ensures true;
    }
}

/*
  requires MayLoop ensures x'=91 & c'=0;*/
{
	if (c > 0) {
		if (x > 100) {
			x = x - 10;
			c--;
		} else {
			x = x + 11;
			c++;
		}
		loop(x, c);
	}
}
