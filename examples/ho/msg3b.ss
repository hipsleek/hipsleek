data cell {
  int x;
}

data chan {
  int y;
}

pred_prim MSG{F}<c:cell>
inv c!=null;

pred_prim CNT<i:int>
inv true;

// "chan" type lost?
// what is the type for res in res::MSG{v::cell<1> & true}<v>?
chan create_msg (int x)
  requires true
  ensures (exists v: res::MSG{v::cell<1> & true}<v> * res::CNT<0>);

/*
chan create_msg{%G}(int x)
  requires true ensures (exists v: res::MSG{%G}<v>);
*/

void send(chan ch, cell c)
  requires ch::MSG{%P}<c>@L * %P * ch::CNT<n>
  ensures ch::CNT<n+1>;

void receive(chan ch, ref cell c)
  requires ch::MSG{%P}<c>@L * ch::CNT<n> & n>0 // do we use c or c'??
    ensures  %P * ch::CNT<n-1> & c'=c;

void main() 
 requires true
 ensures true;
{
  chan ch = create_msg(5);
  dprint;
  cell c = new cell(1);
  cell d;
  dprint;
  receive(ch,d);
  send(ch,c);
  dprint;
}

/*
# msg.ss

parser problem with "chann as result"

P should be free:
         EBase emp&MayLoop[]&{FLOW,(1,27)=__flow}[]
                  EAssume 
                    (exists P: HVar P&{FLOW,(24,25)=__norm})[]
                    



*/
