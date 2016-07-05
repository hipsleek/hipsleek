

void array_copy(arrI base1, arrI base2, int i, int m)
{
  if(i<m){
    upd_arr(base1,i,get_arr(base2,i));
    return array_copy(base1,base2,i+1,m);
  }
  else{
    return;
  }
}
