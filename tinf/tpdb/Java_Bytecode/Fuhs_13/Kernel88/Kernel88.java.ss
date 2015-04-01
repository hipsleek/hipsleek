

data Kernel88
{
Kernel88 next;
}
 void Kernel88_main(String[] args)
{
  int random1 = args[0]_length();
  int random2 = args[1]_length();
  Kernel88_slide88(random1, random2);
}

Kernel88 Kernel88_create(int x)
{
  Kernel88 last;
  Kernel88 current;
  last = current = new Kernel88(null);
  while (--x > 0)
    current = new Kernel88(current);
  return last.next = current;
}

boolean Kernel88_check(int x)
{
  return x % 2 > 0;
}

void Kernel88_slide68(int random1, int random2)
{
  Kernel88 h = Kernel88_create(random1);
  Kernel88 p = h;
  Kernel88 c = p.next;
  while (c != h) {
    Kernel88 o = c;
    c = c.next;
    if (Kernel88_check(random2)) {
      p.next = c;
      o = null;
    } else {
      p = o;
    }
    random2 = random2 / 2;
  }
}

void Kernel88_slide88(int random1, int random2)
{
  Kernel88 h = Kernel88_create(random1);
  Kernel88 p = h;
  Kernel88 c = p.next;
  while (c != h) {
    Kernel88 o = c;
    if (Kernel88_check(random2)) {
      Kernel88 e = o.next;
      p.next = e;
      o = null;
      c = o;
    } else {
      p = o;
    }
    c = c.next;
    random2 = random2 / 2;
  }
}

void Kernel88_slide93(int random1, int random2)
{
  Kernel88 h = Kernel88_create(random1);
  Kernel88 p = h;
  Kernel88 c = p.next;
  while (c != h) {
    Kernel88 o = c;
    if (Kernel88_check(random2)) {
      Kernel88 e = o.next;
      p.next = e;
      o.next = o;
    } else {
      p = o;
    }
    c = c.next;
    random2 = random2 / 2;
  }
}

void Kernel88_slide95(int random1, int random2)
{
  Kernel88 h = Kernel88_create(random1);
  Kernel88 p = h;
  Kernel88 c = p.next;
  while (c != h) {
    Kernel88 o = c;
    c = c.next;
    if (Kernel88_check(random2)) {
      Kernel88 e = o.next;
      p.next = e;
      o.next = o;
    } else {
      p = o;
    }
    random2 = random2 / 2;
  }
}

global String[] Random_args;

int Random_random()
  requires true
  ensures true;

int String_length(String k)
  requires true
  ensures res >=0;