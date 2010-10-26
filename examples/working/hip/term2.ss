
void f(int x, int y)
 case {
  x>0 -> ensures "term":true;
  x<=0 -> ensures "nonterm":false;
}
{  
  if (x>0) return;
   else {
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
