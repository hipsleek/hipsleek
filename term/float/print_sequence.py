#!/usr/bin/python
import math

N = 10

def f(x):
  y = x * x - 1.0
  return y
  
fixpoint = (1 + math.sqrt(5)) / 2
 
x = 0.5;
for i in range(N):
  distance = abs(x - fixpoint)
  print distance
  x = f(x)

