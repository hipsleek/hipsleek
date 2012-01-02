
void del(int n)
  infer @pre [n]
  requires true
  ensures  true; 
{  
    acc(n);
    n=n-1; 
    dprint;
    acc(n);
}

void acc(int n)
  requires n>=1
  ensures true;


void acc2(int n)
  requires n>=2
  ensures true;
