

data Kernel93
{
Kernel93 next;
}
 void Kernel93_main(String[] args)
{
  int random1 = args[0]_length();
  int random2 = args[1]_length();
  Kernel93_slide93(random1, random2);
}

Kernel93 Kernel93_create(int x)
{
  Kernel93 last;
  Kernel93 current;
  last = current = new Kernel93(null);
  while (--x > 0)
    current = new Kernel93(current);
  return last.next = current;
}

boolean Kernel93_check(int x)
{
  return x % 2 > 0;
}

void Kernel93_slide68(int random1, int random2)
{
  Kernel93 h = Kernel93_create(random1);
  Kernel93 p = h;
  Kernel93 c = p.next;
  while (c != h) {
    Kernel93 o = c;
    c = c.next;
    if (Kernel93_check(random2)) {
      p.next = c;
      o = null;
    } else {
      p = o;
    }
    random2 = random2 / 2;
  }
}

void Kernel93_slide88(int random1, int random2)
{
  Kernel93 h = Kernel93_create(random1);
  Kernel93 p = h;
  Kernel93 c = p.next;
  while (c != h) {
    Kernel93 o = c;
    if (Kernel93_check(random2)) {
      Kernel93 e = o.next;
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

void Kernel93_slide93(int random1, int random2)
{
  Kernel93 h = Kernel93_create(random1);
  Kernel93 p = h;
  Kernel93 c = p.next;
  while (c != h) {
    Kernel93 o = c;
    if (Kernel93_check(random2)) {
      Kernel93 e = o.next;
      p.next = e;
      o.next = o;
    } else {
      p = o;
    }
    c = c.next;
    random2 = random2 / 2;
  }
}

void Kernel93_slide95(int random1, int random2)
{
  Kernel93 h = Kernel93_create(random1);
  Kernel93 p = h;
  Kernel93 c = p.next;
  while (c != h) {
    Kernel93 o = c;
    c = c.next;
    if (Kernel93_check(random2)) {
      Kernel93 e = o.next;
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