class e1 extends __Exc {}
class e2 extends e1 {}
class e3 extends e2 {}
class e4 extends e2 {}
class e5 extends e4 {}

class thread extends __Exc{
  int id
  }

void fork(int id, ref int n)
requires true & flow __norm
  ensures eres::thread<id> &  n'=n+1 & flow thread;
{
  n++;
  raise new thread(id);
}

void incXY(ref int x,ref int y)
  requires true & flow __norm
  ensures x'=x+1 & y'=y+1 & flow __norm; //'
{
  int id;
  try{
  fork(id,x); // imitate x++;
  //at this point, need to create concurrent flows
  dprint;
  int abc;
  dprint;
  y++;
  dprint;
  }catch(thread t){ //at catch point, we need both flows
    bind t to (tid) in
    {
      if (tid==id){
        dprint; //at this point, we need to conjoin
      }
    }
  };
}


