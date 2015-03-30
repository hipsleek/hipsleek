

data Kernel95
{
Kernel95 next;
}
 void Kernel95_main(String[] args)
{
  int random1 = args[0]_length();
  int random2 = args[1]_length();
  Kernel95_slide95(random1, random2);
}

Kernel95 Kernel95_create(int x)
{
  Kernel95 last;
  Kernel95 current;
  last = current = new Kernel95(null);
  while (--x > 0)
    current = new Kernel95(current);
  return last.next = current;
}

boolean Kernel95_check(int x)
{
  return x % 2 > 0;
}

void Kernel95_slide68(int random1, int random2)
{
  Kernel95 h = Kernel95_create(random1);
  Kernel95 p = h;
  Kernel95 c = p.next;
  while (c != h) {
    Kernel95 o = c;
    c = c.next;
    if (Kernel95_check(random2)) {
      p.next = c;
      o = null;
    } else {
      p = o;
    }
    random2 = random2 / 2;
  }
}

void Kernel95_slide88(int random1, int random2)
{
  Kernel95 h = Kernel95_create(random1);
  Kernel95 p = h;
  Kernel95 c = p.next;
  while (c != h) {
    Kernel95 o = c;
    if (Kernel95_check(random2)) {
      Kernel95 e = o.next;
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

void Kernel95_slide93(int random1, int random2)
{
  Kernel95 h = Kernel95_create(random1);
  Kernel95 p = h;
  Kernel95 c = p.next;
  while (c != h) {
    Kernel95 o = c;
    if (Kernel95_check(random2)) {
      Kernel95 e = o.next;
      p.next = e;
      o.next = o;
    } else {
      p = o;
    }
    c = c.next;
    random2 = random2 / 2;
  }
}

void Kernel95_slide95(int random1, int random2)
{
  Kernel95 h = Kernel95_create(random1);
  Kernel95 p = h;
  Kernel95 c = p.next;
  while (c != h) {
    Kernel95 o = c;
    c = c.next;
    if (Kernel95_check(random2)) {
      Kernel95 e = o.next;
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