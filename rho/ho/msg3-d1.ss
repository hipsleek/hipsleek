data cell {
  int x;
}

data chan {
  int y;
}

pred_prim MSG{F}<c:cell>
inv c!=null;

pred_prim MSG2<c:cell>
inv c!=null;

// "chan" type lost?
// what is the type for res in res::MSG{v::cell<1> & true}<v>?
chan create_msg (int x)
  requires true
  ensures (exists v: res::MSG{v::cell<1> & true}<v>);

/*
chan create_msg{%G}(int x)
  requires true ensures (exists v: res::MSG{%G}<v>);
*/

void send(chan ch, cell c)
    requires ch::MSG{%P}<c>@L * %P
    ensures  emp;

void receive(chan ch, ref cell c)
    requires ch::MSG{%P}<a>@L // do we use c or c'??
    ensures  %P & c'=c;

void main() 
 requires true
 ensures true;
{
  chan ch = create_msg(5);
  //dprint;
  cell c = new cell(1);
  //cell d;
  //dprint;
  send(ch,c);
  //dprint;
  //receive(ch,c);
  //dprint;
}

/*
# msg3-d1.ss --dis-imm

--dis-imm not working properly as hole still present..

Successful States:
[
 Label: []
 State:Hole[1242]&v_int_40_1241=1 & c_39'!=Cnull & c_39'!=Cnull&{FLOW,(24,25)=__norm}[]


*/
