/*****************************************************
Example from "Alternation for Termination"
William R. Harris et al. (SAS'10)
*****************************************************/

bool rand_bool ()
requires Term
ensures true;

int rand_int ()
requires Term
ensures true;

void f (int d)
case {
  d<=0 -> requires MayLoop ensures true;
  d>0 -> requires Term ensures true;
}
{
  int x, y, k, z = 1;
  loop_1 (k, z);
  loop_2 (x, y, z, d);
  
}

void loop_1 (ref int k, ref int z)
case {
  z>=k -> requires Term ensures z'=z & k'=k;
  z<k -> case {
    z<=0 -> requires Loop ensures false;
		z>0 -> requires Term[k-z] ensures z'>=k & k'=k;
  }
}
{
  if (z<k) {
    z = 2*z;
		loop_1(k, z);
  }
}

void loop_2 (ref int x, ref int y, ref int z, ref int d)
case {
  !(x>0 & y>0) -> requires Term ensures true;
  (x>0 & y>0) -> case {
		d>0 -> requires Term[x, y] ensures true;
		d<=0 -> requires MayLoop ensures true;
  }
}
{
  if (x>0 && y>0) {
    bool b = rand_bool();
	if (b) {
	  x = x-d;
	  y = rand_int(); //y may receive a negative value and loop_2 terminates
	  z = z-1;
	} else {
	  y = y-d;
	}
	loop_2(x, y, z, d);
  }
}
