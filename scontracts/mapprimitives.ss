
void update [T1,T2] (ref mapping(`T1 => `T2) map, `T1 key, `T2 val)
   requires true
   ensures  map'[key]=val;

`T2 select [T1,T2] (mapping(`T1 => `T2) map, `T1 key)
   requires map[key]=val
   ensures  res = val;

void delete [T1,T2] (ref mapping(`T1 => `T2) map, `T1 key)
   requires true
   ensures  map'[key]=ZERO;
