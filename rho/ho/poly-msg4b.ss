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
  ensures (exists v,n: res::MSG{v::cell<n> & n>x}<v> * res::CNT<0>);

/*
 chan  create_msg{%G}(int x)
       requires true 
       ensures (exists v: res::MSG{%G}<v>);


 create[cell]{pred v:cell 
                  ->(exists n: v::cell<n> & n>x)}

*/

Expressive Resource Predicate

// polymorphic resource predicate

chan create[t]{%G}()
    requires true
    ensures (exists v:t : res::MSG{%G[v]}<v>);

void send[t](chan ch, t c)
  requires ch::MSG{%P}<c>@L * %P * ch::CNT<n>
  ensures ch::CNT<n+1>;

void receive[t](chan ch, ref t c)
  requires ch::MSG{%P}<c>@L * ch::CNT<n> & n>0 // do we use c or c'??
  ensures  %P * ch::CNT<n-1> & c'=c;

void main() 
 requires true
 ensures true;
{
  //chan ch = create_msg(5);
  chan ch = create[cell]{pred v
                ->(exists n: v::cell<n> & n>5)}()
  dprint;
  cell c = new cell(6);
  cell d;
  dprint;
  send[cell](ch,c);
  receive[cell](ch,d);
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
