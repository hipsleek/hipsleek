data pair{int x; int y;}

/*int foo(pair p)
requires p::pair<a,b> & a+b>0
ensures res = b;
{
        //dprint;
        int temp = p.x + p.y;
        dprint;
        if (temp > 0) {
                dprint;
                return p.y;
        }
        dprint;
        return -1;
}*/

int first(pair p)
requires p::pair<a,_> 
ensures p::pair<a, _> &  res = a;
{
        int tmp=p.x;
        dprint;
        return tmp;
}

int addtwice(pair p)
requires p::pair<a,_> 
ensures res = a;
{
       int t1 = first(p);
       dprint;
       int t2 = first(p);
       dprint;
       int r=t1+t2;
       dprint;
       return t1;
}