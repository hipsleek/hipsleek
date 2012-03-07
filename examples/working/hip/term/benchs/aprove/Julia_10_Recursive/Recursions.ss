int rand_int ()
requires Term
ensures true;

void main () 
requires Term
ensures true;
{
	rec0(0, rand_int());
}

void rec0 (int i, int stop) 
case {
	i>stop -> requires Term ensures true;
	i<=stop -> requires Term[stop-i] ensures true;
}
{
	if (i <= stop) {
		rec1(0, 2*i, i);
    rec0(i+1, stop);
  }
}

void rec1 (int j, int stop, int i) 
case {
	j>stop -> requires Term ensures true;
	j<=stop -> requires Term[stop-j] ensures true;
}
{
	if (j <= stop) {
		rec2(i+j, 0, i, j);
    rec1(j+1, stop, i);
  }
}

void rec2 (int k, int stop, int i, int j) 
case {
	k>=stop -> requires Term[k-stop] ensures true;
	k<stop -> requires Term ensures true;
}
{
	if (k >= stop) {
		rec3(0, 2*i + 3*j + 4*k, i, j ,k);
    rec2(k-1, stop, i, j);
  }
}

void rec3 (int l, int stop, int i, int j, int k) 
case {
	l>stop -> requires Term ensures true;
	l<=stop -> requires Term[stop-l] ensures true;
}
{
	if (l <= stop) {
		rec4(1000*i+100*j+10*k+l, 0);
    rec3(l+1, stop, i, j, k);
  }
}

void rec4 (int m, int stop) 
case {
	m>=stop -> requires Term[m-stop] ensures true;
	m<stop -> requires Term ensures true;
}
{
	if (m >= stop)
  	rec4(m-1, stop);
}

