/*
  Note: there are two ways to create new heap
  (1) tranditional new cell(bound,value), where the first arg
  is the bound of bperm
  (2) define a wrapper newCell(bound,value)
 */

data cell {int val;}

//************************************
// WRAPPER FUNCTION
cell newCell(int bound,int value)
  requires bound>0
  ensures res::cell(bound,bound,0)<value>;

// WRAPPER FUNCTION
void destroyCell(ref cell ce)
  requires ce::cell(c,t,a)<_> & c=t+a
  ensures ce'=null;//'
//************************************

//SUCCESS
int readCell(cell c)
  requires c::cell(1,2,0)<v>
  ensures c::cell(1,2,0)<v> & res=v;
{
  int x;
  x=c.val;
  //dprint;
  return x;
}

//SUCCESS
int updateCell(cell c,int newv)
  requires c::cell(2,2,0)<v>
  ensures c::cell(2,2,0)<newv> & res=v;
{
  int x;
  x=c.val;
  //dprint;
  c.val=newv;
  //dprint;
  return x;
}

//FAIL-1
void updateCellFail(cell c,int newv)
  requires c::cell(1,2,0)<v>
  ensures c::cell(1,2,0)<newv>;
{
  //dprint;
  int x;
  c.val=newv; //FAIL here due to insufficient permission
  //dprint;
}

//FAIL-1
void destroyCellFail(cell c)
  requires c::cell(1,2,0)<v>
  ensures true;
{
  //dprint;
  destroyCell(c);
}

//SUCCESS
void testNewCell()
  requires true
  ensures true;
{
  //create a cell with permission total 2 and initial value 0
  cell c = new cell(2,0);
  c.val=5;
  //dprint;
  destroyCell(c);
  //dprint;
}

//SUCCESS
void testNewCell2()
  requires true
  ensures true;
{
  //create a cell with permission total 2 and initial value 0
  cell c = newCell(2,0);
  c.val=5;
  //dprint;
  destroyCell(c);
  //dprint;
}
