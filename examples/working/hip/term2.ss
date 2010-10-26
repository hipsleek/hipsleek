
void f(int x, int y)
 case {
  x>0 -> ensures "term":true;
  x<=0 -> ensures "nonterm":false;
}
{  
  if (x>0) {
     assert true;
     return h(x,y);
  } else {
         int x1=x-1;
         int y1=y;
         assert "term": false;
         g(x1,y1);
        }
}

void g(int x, int y)
  requires x+1<=0
  ensures "nonterm":false;
{     
       int x1=x+1; 
       int y1=y;
       assert "term": false;
       f(x1,y1);     
}


void h(int x, int y)
  requires true
  ensures "term":true;
{     
  if (y>0) {
    int x1=x;int y1=y-1;
    assert y1'>=0;
    assert y-y1'>0;
    h(x1,y1);
  } else return;
}
