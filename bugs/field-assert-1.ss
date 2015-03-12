data pair {
 int x;
 int y;
}

global int p;

int main()
  requires  true
  ensures "pp": true;
{
 pair p = new pair(2, 3);
 pair q = p;
 q.x = 3;
 //assert (q'.x = 3) ;
 dprint "";
 assert q'::pair<a,_>&a=4; //
 dprint;
 return 1;
}
