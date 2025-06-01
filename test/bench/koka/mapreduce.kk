module mapreduce

import std/os/env
import std/os/task
import std/num/int32
import std/num/random

fun calcone(n : int) : pure int
  var i := 0;
  var res := 0;
  while { i < n % 67 }
    i := i + 1
    res := res + (n * n + n / 177)
  res

fun calconefn(n : int) : pure promise<int>
  task{ calcone(n) }

fun calc(n : int) : pure promise<int>
  list(0, 1000).map(calconefn).wait_all.transform(fn(l) foldl1(l, fn(i : int, j : int) if i < j then j else i))


pub fun main()
  val lst = list(0, 100)
  val result = lst.map(calc).wait_all.transform(fn(l) foldl1(l, fn(i, j) if i < j then j else i)).await
  show(result)
