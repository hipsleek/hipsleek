data cell {int val;}

//SUCCESS
int readCell(cell c)
  requires c::cell(1,2,0)<v>
  ensures c::cell(1,2,0)<v> & res=v;
{
  int x;
  x=c.val;
  dprint;
  return x;
}

//SUCCESS
int updateCell(cell c,int newv)
  requires c::cell(2,2,0)<v>
  ensures c::cell(2,2,0)<newv> & res=v;
{
  int x;
  x=c.val;
  dprint;
  c.val=newv;
  dprint;
  return x;
}

//FAIL-1
void updateCellFail(cell c,int newv)
  requires c::cell(1,2,0)<v>
  ensures c::cell(1,2,0)<newv>;
{
  dprint;
  int x;
  c.val=newv; //FAIL here due to insufficient permission
  dprint;
}

void destroyCell(ref cell ce)
  requires ce::cell(c,t,a)<_> & c=t+a
  ensures ce'=null;//'

//FAIL-1
void destroyCellFail(cell c)
  requires c::cell(1,2,0)<v>
     ensures true;
{
  dprint;
  destroyCell(c);
}

//SUCCESS
void newCell()
  requires true
  ensures true;
{
  //create a cell with permission total 2 and initial value 0
  cell c = new cell(2,0);
  c.val=5;
  dprint;
  destroyCell(c);
  dprint;
}
