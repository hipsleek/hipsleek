data MyP {
   int j;
   int k;
}

MyI<j,k,x> == self::MyP<j,k> & j<=x<=k inv j<=x<=k;

lemma "A" self::MyI<j,k,x> & j<=x<=k -> self::MyP<j,k>;

void p(MyP p) 
  requires p::MyP<10,12>
  ensures p::MyI<_,_,11>;
  requires p::MyP<10,12>
  ensures p::MyI<_,_,x> & (x=10 | x=12);
  requires p::MyI<10,12,11>
  ensures p::MyI<_,_,x> & (x=10 | x=12);
 // requires p::MyI<10,12,11>
 // ensures p::MyI<_,_,12>;
{
}

MyP m() 
  //requires true
  //ensures res::MyI<1,0,x>;
  requires true
  ensures res::MyP<1,0>;
{ return new MyP(1,0);
}

MyP n() 
  //requires true
  //ensures res::MyI<1,0,x>;
  requires true
  ensures res::MyI<_,_,x> & (x=10 | x=11);
  requires x=10
  ensures res::MyI<_,_,x>;
  //requires true
  //ensures res::MyI<_,_,_>;
{ return new MyP(10,12);
}


