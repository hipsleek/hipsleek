data mutex {
  int is_locked;
}

void err() requires true ensures true;

void mutex_lock (mutex a)
  requires a::mutex<0>
  ensures a::mutex<1>;
{
  int tmp = a.is_locked;
  if (tmp==1) {
    err(); 
    return;
  }
  else {
    a.is_locked = 1;
    return;
  }
}

void mutex_unlock (mutex b)
  requires b::mutex<1>
  ensures b::mutex<0>;
{
  int tmp = b.is_locked;
  if (tmp!=1) {
    err(); 
    return;
  }
  else {
    b.is_locked = 0;
    return;
  }
}

void main()
  requires true
  ensures true;
{
  mutex m = new mutex(0);  
  mutex_lock(m);
  mutex_unlock(m);
  return;
}

